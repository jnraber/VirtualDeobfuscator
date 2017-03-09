#------------------------------------------------------------------------------
# Virtual Deobfuscator (VD)
# author:  Jason Raber
# company: HexEffect, LLC www.hexeffect.com  2013
# Virtual Deobfuscator is free software: you can redistribute it and/or modify 
# it under the terms of the GNU General Public License as published by the Free 
# Software Foundation, either version 3 of the License, or (at your option) any 
# later version.
#
# Virtual Deobfuscator is distributed in the hope that it will be useful, but 
# WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY 
# or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License along with 
# Virtual Deobfusctor. If not, see http://www.gnu.org/licenses/.
# Notes:
# Make sure to install Python package lxml http://lxml.de/installation.html
# Python 2.7
#------------------------------------------------------------------------------

import os
import string
import sys
import re
import utils as u
import cluster
import argparse

#------------------------------------------------------------------------------
# Globals/Consts
#------------------------------------------------------------------------------
DB       = "vd.xml"     # VD's database
IR_FILE  = "vd_IR.txt"  # Internal rep of runtrace...remove special chars

#------------------------------------------------------------------------------
# Header
#------------------------------------------------------------------------------
def hdr(isClustering, dbgr, test_file):

    etree = pre_run(isClustering, test_file)

    if isClustering == False:
        print "Parsing"
        if dbgr == u.OLLY:
            sys.stdout.write("- runtrace for OllyDbg 2.0")
        elif dbgr == u.IMMUNITY:
            sys.stdout.write("- runtrace for Immunity/OllyDbg 1.10 debugger")
        elif dbgr == u.WINDBG:
            sys.stdout.write("- runtrace for WinDbg")
        else:
            print "!! Unknown debugger run trace"

    return etree

#------------------------------------------------------------------------------
# Footer
#------------------------------------------------------------------------------
def footer(cnt):
    print "\n----------------------------------------------------------------"
    print "lines parsed " + str(cnt)
    print "----------------------------------------------------------------"

#------------------------------------------------------------------------------
# Pre Run.  Load appropriate packages etc. XML parser
#------------------------------------------------------------------------------
def pre_run(isClustering, testfile):

    # check version of python running
    if not sys.version_info[:2] == (2, 7):
        u.vd_error("U need python 2.7 installed to run Virtual Deobfuscator")

    print "\nLoading packages..."

    # clean up Virtual Deob database and testing file
    if isClustering == False:
        if os.path.exists(DB):
            os.remove(DB)
        if os.path.exists(testfile):
            os.remove(testfile)

    # use lxml if it's available -- faster
    from lxml import etree
    return etree

#------------------------------------------------------------------------------
# OllyDbg 2.0 - Parse this runtrace format
# format: ['main', '0040106D', 'PUSH', 'OFFSET', '004021C8', 'ESP=0018FF84']
#          thread | virtual addr | instruction | effect on registers
#------------------------------------------------------------------------------
def parse_OllyDbg_20(db_file, line, etree):

    # remove special characters that would hose up the xml output (<, >, &)
    line = re.sub(r'[\<\>\&]', "", line)
    line = filter(lambda x: x in string.printable, line)

    # remove whitespaces
    # i.e OllyDbg output
    # main  0040108D    PUSH EBX              ESP=0018FF54
    # becomes
    # ['main', '0040106D', 'PUSH', 'OFFSET', '004021C8', 'ESP=0018FF84']
    ins_lst = line.strip().split()
    if len(ins_lst) == 0:
        return

    # assign fields
    thread = ins_lst[0]
    va     = ins_lst[1]

    registers = ""

    # look for register effects of instruction.  The delimeter to look for is
    # = or ; otherwise it is part of the mnem
    cnt = 3
    mnemonic = ins_lst[2] # at this pos it is a mnem...now grab the rest of op
    for item in ins_lst[3:]:
        if item.find(";") != -1 or item.find("=") != -1:
            for x in ins_lst[cnt:]:
               registers += x + " "
            break
        else:
            mnemonic += " " + item

        cnt += 1

    create_xml(db_file, etree, thread, va, mnemonic, registers)


#------------------------------------------------------------------------------
# Immunity/OllyDbg 1.10 Debugger - Parse this runtrace format
#          virtual addr | thread | instruction | effect on registers and cmts
#------------------------------------------------------------------------------
def parse_Immunity_Olly110(db_file, line, etree):

    # remove special characters that would hose up the xml output (<, >, &)
    line = re.sub(r'[\>\<\&]', " ", line)

    # remove whitespaces
    # i.e Immunity output
    # 00401077 Main     XOR EBX,EBX  ; EBX=00000000
    # becomes
    # ['00401077', 'Main', 'XOR', 'EBX,EBX', ';', 'EBX=00000000']
    ins_lst = line.strip().split()
    if len(ins_lst) == 0:
        return

    # a special case of how Immunity handles instructions that are API calls
    # __security_init_c MOV EDI,ED
    # ['__security_init_c', 'MOV', 'EDI,EDI']
    if (u.is_number_hex(ins_lst[0]) == False):
        ins_lst.insert(1, 'Unknown')

    # assign attributes
    va     = ins_lst[0]
    thread = ins_lst[1]
    registers = ""

    i = 2
    # look for register effects of instruction.  The delimeter to look for is ;
    # otherwise it is part of the mnem
    mnemonic = ins_lst[2] # at this pos it is a mnem...now grab the rest of op
    for item in ins_lst[3:]:
        i += 1
        if item.find(";") != -1:
            registers += ' '.join(ins_lst[i:])
            #print registers
            break
        else:
            mnemonic += " " + item

    create_xml(db_file, etree, thread, va, mnemonic, registers)


#------------------------------------------------------------------------------
# WinDbg - Parse this runtrace format
#          thread
#          virtual addr | opcode | instruction
# for now I am going to drop the opcode as it is not important or relevant
#------------------------------------------------------------------------------
def parse_WinDbg(db_file, line, etree):

    # remove special characters
    # hello!__tmainCRTStartup: becomes
    # hello __tmainCRTStartup:
    line = re.sub(r'[\!]', " ", line)

    # remove whitespaces
    # i.e WinDbg output
    # hello __tmainCRTStartup:
    # 0040106b 6a10            push    10h
    # becomes
    # ['hello', __tmainCRTStartup]
    # ['0040106b', '6a10', 'push', '10h']
    ins_lst = line.strip().split()
    if len(ins_lst) == 0:
        return

    # Skip lines that start with eax=, eip=, or cs=
    reg_str = ins_lst[0][:4]
    cs_str = ins_lst[0][:3]
    if reg_str == "eax=" or reg_str == "eip=" or cs_str == "cs=":
        return

    # The thread is on the line above so store that off
    # hello mainCRTStartup+0x5:
    if (u.is_number_hex(ins_lst[0]) == False):
        parse_WinDbg.thread = ins_lst[0]
        return

    # assign attributes
    va = ins_lst[0]
    registers = "None"

    # ins_lst[1] is the opcode.  We are going to skip that as it is not
    # important to Virtual Deobfuscator

    mnemonic = ins_lst[2] # at this pos it is a mnem...now grab the rest of op
    for item in ins_lst[3:]:
        mnemonic += " " + item

    create_xml(db_file, etree, parse_WinDbg.thread, va, mnemonic, registers)

parse_WinDbg.thread = ""

#------------------------------------------------------------------------------
# Write out instruction line into XML format to file called vd.xml
# Format will be:
#<ins num="1">
#  <thread>main</thread>
#  <va>0040106D</va>
#  <mnem>PUSH OFFSET 004021C8</mnem>
#  <regs>ESP=0018FF84 </regs>
#</ins>
#------------------------------------------------------------------------------
def create_xml(db_file, etree, thread, viraddr, mnemonic, registers):

    ins       = etree.Element("ins")
    ins.text  = str(create_xml.ins_cnt)
    thd       = etree.SubElement(ins, "thread")
    thd.text  = thread
    va        = etree.SubElement(ins, "va")
    va.text   = viraddr
    mnem      = etree.SubElement(ins, "mnem")
    mnem.text = mnemonic

    # if no registers then give it a filler
    if registers == "":
        registers = "None"

    reg       = etree.SubElement(ins, "regs")
    reg.text  = registers

    #print(etree.tostring(ins, pretty_print=True))
    #print(etree.tostring(ins))

    db_file.writelines(etree.tostring(ins))
    db_file.writelines("\n")

    create_xml.ins_cnt += 1

create_xml.ins_cnt = 0

#------------------------------------------------------------------------------
# Read in instructions that are stored in XML format
# testfile is used to verify that we correctly read in the vd.xml -> it removes
# tags <ins> ect and outputs to a file(testfile)
#------------------------------------------------------------------------------
def read_xml(etree, testfile, dbgr, cluster):

    out_s = ""
    test_file = ""

    print "\nread_xml"

    # for verification that we read the vd.xml the user used '-t testXML.txt'
    if testfile != "":
        sys.stdout.write("- reading %s and writing  %s" % (DB, testfile))
        test_file = open(testfile, "a")
    else:
        sys.stdout.write("- reading %s" % (DB))

    thread   = ""
    va       = ""
    mnem     = ""
    regs     = ""
    line_num = 0

    cnt = 0


    # for very large runtraces etree.parse crashes...probably b/c it runs
    # out of memory
    #tree = etree.parse('vd.xml')
    tree = etree.iterparse('vd.xml', events=('end',))

    for action, elem in tree:
        #print elem.tag, elem.text

        if elem.text is not None:
            if elem.tag == 'thread':
                thread   = ""
                va       = ""
                mnem     = ""
                regs     = ""
                out_s    = ""
                line_num = 0

            if elem.tag == 'thread':
                thread = elem.text
            elif elem.tag == 'va':
                va = elem.text
            elif elem.tag == 'mnem':
                mnem = elem.text
                if not mnem:
                    print va, thread
                    utils.vd_error("ill formed line - fix before creating " \
                                   "database vd.xml")

            elif elem.tag == 'regs':
                regs = elem.text
                # now print out to our outfile to test correctness
                if testfile != "":
                    if dbgr == u.OLLY:
                        if regs == "None":
                            out_s = thread + " " + va + " " + mnem + "\n"
                        else:
                            out_s = thread + " " + va + " " + mnem + " " \
                                    + regs + "\n"
                    elif dbgr == u.IMMUNITY:
                        if thread == 'Unknown':
                            thread = ""
                        if regs == "None":
                            out_s = va + " " + thread + " " + mnem + "\n"
                        else:
                            out_s = va + " " + thread + " " + mnem + " " \
                                    + regs + "\n"
                    elif dbgr == u.WINDBG:
                            out_s = va + " " + thread + " " + mnem + "\n"
                    else:
                        utils.vd_error("Make sure to declare a debugger -d switch")
            elif elem.tag == 'ins':
                line_num = elem.text


                # append to frequency table
                cluster.add_freq(va, line_num)
                cluster.cluster_lst.append(va)

                if test_file != "":
                    test_file.writelines(out_s)

                cnt += 1
                if cnt > 5000:
                    sys.stdout.write(".")
                    sys.stdout.flush
                    cnt = 0

            #print "elem: " + elem.tag, elem.text

            # eliminate empty refs from  root node
            elem.clear()
            while elem.getprevious() is not None:
                del elem.getparent()[0]

    if test_file != "":
        test_file.close()


#------------------------------------------------------------------------------
# create an Internal Representation (IR) of the runtrace called 'vd_IR.txt'
# remove special characters such as '<', '>', '&' and convert to 'vd_IR.txt'
# NOTE: I use this vd_in.txt to do a diff on my generated file 'test.txt'
#       which is created by read_XML...as a way to test that I am creating
#       the XML from the runtrace correctly.
#       i.e. diff test.txt vd_in.txt
#------------------------------------------------------------------------------
def create_IR(runtrace):

    if os.path.exists(IR_FILE):
        os.remove(IR_FILE)

    print ""
    sys.stdout.write("formating runtrace for Virtual Deobfuscator > %s " \
                     % IR_FILE)


    try:
        ofile = open(IR_FILE, "a")
    except IOError as exc:
        raise IOError("%s: %s" % (IR_FILE, exc.strerror))

    # verify parameters are correct
    if not os.path.exists(runtrace):
        u.vd_error("No such runtrace file: " + runtrace)

    try:
        with open(runtrace, "r") as ifile:
            cnt = 0
            while 1:
                line = ifile.readline()
                if len(line) == 0:
                    break

                line = line.strip("\n")

                # remove special chars from runtrace
                line = re.sub(r'[\<\>\&]', " ", line)
                line = filter(lambda x: x in string.printable, line)

                ofile.writelines(line)
                ofile.writelines("\n")
                cnt += 1
                # basic progress bar
                if cnt > 5000:
                    sys.stdout.write(".")
                    sys.stdout.flush()
                    cnt = 0

            ifile.closed
            ofile.closed

    except IOError as exc:
        raise IOError("%s: %s" % (runtrace, exc.strerror))
        sys.exit()

#------------------------------------------------------------------------------
# Iterate through all the backtrace files to reverse the process and build
# the original run trace.  I use this for validation
#------------------------------------------------------------------------------
def build_complete_backtrace(round, cluster):
    round_idx = round
    if os.path.exists(u.BT_ALL_FILE):
        os.remove(u.BT_ALL_FILE)
        try:
            os.remove(u.VALIDATE_FILE)
        except:
            print "no " + u.VALIDATE_FILE

    if round > 0:
        print "Create Complete Backtrace"
        while round_idx:
            print "- [round " + str(round_idx) + "]"
            cluster.backtrace_all(round_idx)
            round_idx -= 1
        cluster.validate_backtrace_all(False)

#------------------------------------------------------------------------------
# As a minor enhancement I added a new switch '-x' that reformats a runtrace
# and removes ill formed lines found in runtraces such as new lines (sometimes
# found in printf statements).  When using -x it creates a new file called
# 'rt_formatted.txt'.
#
# e.g.
# "ESP=addr"
#------------------------------------------------------------------------------
def reformat_rt(runtrace):
    try:
        new_rt = open(u.FORMATTED_FILE, "w")
    except IOError as exc:
        raise IOError("%s: %s" % (u.FORMATTED_FILE, exc.strerror))
    try:
        rt = open(runtrace, "r")
    except IOError as exc:
        raise IOError("%s: %s" % (runtrace, exc.strerror))

    line_cnt = 0
    while 1:
        line_cnt += 1
        line = rt.readline()
        line_len = len(line)
        if line_len == 0:
            break
        #line = line.strip("\n")

        if line_len < 38:
            print "\nSkipping ill formed line: ", line, line_cnt
            continue
        else:
            new_rt.writelines(line)

    print("New runtrace created called: rt_formatted.txt")
    sys.exit(2)

#------------------------------------------------------------------------------
# Main
#------------------------------------------------------------------------------
def main():

    print "\n------------------------------------------------------------------"
    print "|                  Virtual Deobfuscator ver 1.0                  |"
    print "|                            HexEffect                           |"
    print "------------------------------------------------------------------\n"

    run_clustering = False
    cleanup_rt     = False  # clean up runtrace of ill formated lines
    unfolding      = False
    build_sections = False
    section        = 0
    dbgr           = -1

    #--------------------------------------------------------------------------
    # Handle command line arguments
    testXML = ''

    epilog = '''
------------------------------------------------------------------

Example:
  Import a trace with:

      VirtualDeobfuscator.py -i trace.txt -d 1 -t testXML.txt

  Output will be:

      vd.xml       VD database
      vd_IR.txt    just the runtrace with special chars removed
      testXML.txt  file that is used to test the XML parsing

  Compare testXML.txt and vd_IR.txt:

      diff testXML.txt vd_IR.txt
'''

    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=epilog)
    import_args = parser.add_argument_group(
        'Import', 'These arguments are used to import a trace file.')
    import_args.add_argument(
        '-i', '--ifile', help='A runtrace file created by a debugger')
    import_args.add_argument(
        '-d', '--debugger', help='Debugger: 1 = Olly 2.0, 2 = Immunity/Olly '
        '1.0, 3 = WinDbg', type=int, choices=(1, 2, 3))
    import_args.add_argument(
        '-t', '--testXML', help='A test file that can be used to verify trace '
        'file conversion to XML', default='')
    import_args.add_argument(
        '-x', '--cleanup', action='store_true', default=False,
        help='Cleanup the runtrace')

    cluster_args = parser.add_argument_group(
        'Clustering', 'These arguments are used to perform clustering on an '
        'imported trace.')
    cluster_args.add_argument(
        '-c', '--cluster', action='store_true', default=False,
        help='Run clustering on a database')
    cluster_args.add_argument(
        '-u', '--unfold', action='store_true', default=False,
        help='Unfold clusters')
    cluster_args.add_argument(
        '-s', '--size', type=int, help='Decompose sections of clusters '
        'according to this filter size')
    args = parser.parse_args()

    if not (args.ifile or args.cluster):
        parser.error('''You must specify a trace file (with -i) or
clustering mode (-c).''')

    runtrace = args.ifile
    testXML = args.testXML
    cleanup_rt = args.cleanup
    dbgr = args.debugger
    run_clustering = args.cluster
    unfolding = args.unfold
    section = args.size
    build_sections = args.size is not None

    #----------------------------------------------------------------------
    # print out header info
    etree = hdr(run_clustering, dbgr, testXML)

    #--------------------------------------------------------------------------
    # verify parameters are correct
    if run_clustering == False:
        if not os.path.exists(runtrace):
            u.vd_error("No such runtrace file: " + runtrace)

        if dbgr > 3:
            u.vd_error("Unknown <debugger>: supported OllyDbg 2.0 = 1, " \
                     "Immunity = 2, WinDbg = 3")

        #----------------------------------------------------------------------
        # generate intermediate representation file of runtrace...used for
        # testing XML parsing and reading
        if testXML != "" and (dbgr == u.OLLY or dbgr == u.IMMUNITY):
            create_IR(runtrace)

        if build_sections and section <=0:
            u.vd_error("Cluster section filter must be greater than zero")

        try:
            db_file = open(DB, "a")
        except IOError as exc:
            raise IOError("%s: %s" % (DB, exc.strerror))

        db_file.writelines("<root>\n")

    #--------------------------------------------------------------------------
    # clean up bad lines in runtrace
    if cleanup_rt:
        reformat_rt(runtrace)

    #--------------------------------------------------------------------------
    # parse runtrace
    if run_clustering == False:

        with open(runtrace, "r") as ifile:

            line_cnt = 0
            cnt = 0
            line_cnt = 0

            while 1:
                line_cnt += 1
                line = ifile.readline()
                line_len = len(line)
                if line_len == 0:
                    break

                line = line.strip("\n")

                #--------------------------------------------------------------
                # OllyDbg 2.0
                if dbgr == u.OLLY:
                    # check for end of runtrace
                    if line == "--------  End of session" or \
                       line == "--------  Logging stopped":
                        break

                    if line_len < 38:
                        print "\nIll formed line: ", line, line_cnt
                        print "Use option -x to remove bad lines from runtrace"
                        u.vd_error("PLEASE Fix line to continue")

                    if line_cnt == 1:
                        tmp_lst = line.strip().split()
                        # the first string should be <thread> i.e. 'main'
                        if tmp_lst[0] == "Address":
                            u.vd_error("Incorrect runtrace format for Olly")
                    parse_OllyDbg_20(db_file, line, etree)
                #--------------------------------------------------------------
                # Immunity/OllyDbg 1.10 debugger
                elif dbgr == u.IMMUNITY:
                    # check for end of runtrace
                    if line == "    Run trace closed" or \
                       line.find("Process terminated") != -1:
                        break

                    if line_len < 21:
                        print "\nSkipping ill formed line: ", line, line_cnt
                        u.vd_error("PLEASE Fix line to continue")

                    # Skip first line for Immunity runtrace
                    # Address  Thread   Command  ; Registers and comments
                    if line_cnt == 1:
                        # Verify if correct format for Immunity runtrace
                        if line.find('Address') == -1:
                            u.vd_error("Incorrect runtrace format for Immunity")
                        continue
                    parse_Immunity_Olly110(db_file, line, etree)
                #--------------------------------------------------------------
                # WinDBG
                elif dbgr == u.WINDBG:
                    # check for end of runtrace
                    if line.find("logclose") != -1:
                        break

                    if line_len < 45:
                        print "\nSkipping ill formed line: ", line, line_cnt
                        u.vd_error("PLEASE Fix line to continue")

                    # Skip two lines for WinDbg runtrace
                    # Opened log file 'C:path\...\wd_hello_o.txt'
                    # 0:000> pa 40118B
                    if line_cnt < 2:
                        continue
                    parse_WinDbg(db_file, line, etree)
                else:
                    u.vd_error("Make sure to declare a debugger -d switch")

                cnt += 1
                if cnt > 5000:
                    sys.stdout.write(".")
                    sys.stdout.flush
                    cnt = 0

            ifile.closed

            # tack on </root> endo of xml doc
            db_file.writelines("</root>\n")
            db_file.close()

            #just for testing, parse back in and write to a temp file to diff
            read_xml(etree, testXML, dbgr, cluster)

            footer(line_cnt)

    #--------------------------------------------------------------------------
    # Cluster
    if run_clustering == True:
        if not os.path.exists(DB):
            u.vd_error("No such database file: " + DB)

        #------------------------------------------------------------------
        # No files read in...already have the xml file
        #------------------------------------------------------------------
        read_xml(etree, testXML, dbgr, cluster)

        cluster.print_cluster(-1, False)

        round = 0
        cluster.build_freq_graph(round)
        cluster.print_freq_graph(round, False)

        cluster.compress_basic_blocks_loop(round)
        cluster.print_compress_window(round, False)
        cluster.print_compress_backtrace(round, False)

        cluster.compress_create_new_cluster(round)
        cluster.compress_backtrace(round, False)

        cluster.cluster_lst = cluster.new_cluster_lst[:]
        cluster.print_cluster(round, False)

        round = 1

        cluster.build_freq_graph(round)
        cluster.print_freq_graph(round, False)

        while 1:
            print ("\nGreedy round %s:------------------------------" \
                    % u.id_round[round])
            greedy = cluster.greedy_new_cluster(round)
            if greedy and round < 26:
                cluster.cluster_lst = cluster.new_cluster_lst[:]
                cluster.print_cluster(round, False)

                cluster.print_greedy_backtrace(round, False)
                cluster.greedy_backtrace(round, False)
                build_complete_backtrace(round, cluster)

                # UNFOLDING
                if unfolding:
                    unfold = cluster.unfold_single_clusters(round)
                    if unfold:
                        cluster.cluster_lst = cluster.new_cluster_lst[:]

                round += 1
                cluster.build_freq_graph(round)
                cluster.print_freq_graph(round, False)

            else:
                # temp
                cluster.final_assembly(round-1, etree, dbgr)
                cluster.chunking_clusters(etree, dbgr)

                if build_sections:
                    cluster.chunking_sections(etree, dbgr, section)

                print ("\nClustering done\n")
                sys.exit(2)


if __name__ == "__main__":
    main()
