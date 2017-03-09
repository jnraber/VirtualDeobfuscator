#------------------------------------------------------------------------------
# Virtual Deobfuscator Clustering
# author:  Jason Raber
# company: HexEffect 2013
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
# Notes: Sorry these comments are so long, but it is complicated...I swear!
#
# How it works
# Step 1: Frequency Graph - freq_graph[]
# Read in clusters and create a frequency association that links the instruction
# line numbers with cluster ids.
#    hash key: virtual address or cluster id
#    hash value: line numbers
#
# cluster  line numbers
# 4113D3 - [13]
# 4113D5 - [44, 77, 115, 148] <- This ins @ 4113d5 occurs on lines 44, 77, etc
# 4113D8 - [45, 78, 116, 149]    it is the beginning of a basic block
# 4113DB - [46, 79, 117, 150]
# 4113DE - [14, 47, 80, 118, 151] <------- A new basic block begins
#
#
#------------------------------------------------------------------------------
# COMPRESS BASIC BLOCKS (only done once)
#------------------------------------------------------------------------------
# Step 2:
# This method is used only once as a quick way to compress basic blocks found
# in loops...look above at the freq_graph[] in step 1.  As you can see from the
# structure, we have a new basic block at 0x4113DE...This frequency graph
# is built from sample_loop_exe.exe.  If you disassemble this file and go to
# address 0x411ED5 you will see it is a destination address or beginning of a
# basic block.  Now you also see that in that basic block contains 0x4113D8 and
# 0x4113DB.  Now so long as this basic block has sequential line numbers and
# the same count of line numbers then we can compress the entire basic block
# into a cluster a16_#3.
#
# Window size - window[] - Table of window sizes for each cluster with an
#                          cluster id
#
# cluster    window size    new cluster id
# 4113A1   -   [(1,           4113A1)]
# 4113A3   -   [(1,           4113A3)]
#  ....
# 4113D3   -   [(1,           4113D3)]
# 4113D5   -   [(3,           a16_#3)]  <--- our new cluster with size 3
#
# see compress_basic_blocks_loop() for more details
#
#------------------------------------------------------------------------------
# GREEDY CLUSTERS (repeated until it can find no more clusters)
#------------------------------------------------------------------------------
#
# Step 2:
# Greedy clustering looks at the cluster list, then iterates through this list
# looking for more matches.  It references the freq graph to see if there is
# any duplicate sequential line matches.  If it finds more refs then we are in
# buisness
#
# i.e.
# 004113A0
# a_a1_#2 <- a_a1_#2 + a_a2_#3 match - will become new cluster b1___#5
# a_a2_#3
# a_a1_#2 <- a_a1_#2 + a_a2_#3 match - will become new cluster b1___#5
# a_a2_#3
# a_a1_#2 <- no match, but could be another match for a1,a3
# a_a3_#8
#
#------------------------------------------------------------------------------
# Optional - Backtracing
#------------------------------------------------------------------------------
# I build data structures bt_window[] and bt_greedy[] to backtrace or
# reconstruct our clusters into original form.  The idea is that I can verify
# that my clustering is working
#
#------------------------------------------------------------------------------
# Last clustering step - output new cluster list
#------------------------------------------------------------------------------
# Step 3: New Clusters - new_cluster_lst[]
# Final cluster list generated from alg. compress_basic_blocks_loop() or
#                                        greedy_new_cluster()
#     line number       new cluster id
#       13        -       004113D3
#       14        -       b1___#7
#       15        -       b2___#4
#
# Clusters - cluster_lst[] - records line number and cluster id
# 'a' - a cluster id is constructed by starting with the round (a, b, c) = alpha
# '12' - and appending a unique number (1, 2, 3) = ascending numbers
# '_' - then adding "_" to show depth (easier to see when looking at clusters)
# '#5' - finally, appending the cluster size (#3, #16)
# i.e.  a16_#5
#     a = round 1, '16' = sixteenth cluster, '_' = depth, '#5' = contains 5 ins
#
#     line numbers     cluster id
#         13        -     4113D3  <- VA if no cluster
#         14        -     a15_#2  <- cluster id
#         15        -     a16_#5
#
# From here we repeat the process...Generate a freq_graph from the
# new_cluster_lst...Then cluster_lst = new_cluster_lst after a cluster_read()
#
#------------------------------------------------------------------------------
# Final step - 'final_assembly.txt'
#------------------------------------------------------------------------------
# Honestly, I check this file after clustering is done.  This has the clusters
# but it also pulls out of our database vd.xml the instructions and registers
# effects from that run.
# i.e. 'final_assembly.txt'
#
# 4113D3 JMP SHORT 004113DE
# c1______#11
# f1_______________#47       <--- cluster
# a21_#2
# 411411 MOV EAX,DEADBEEF    <--- This is what we are interested in
# f1_______________#47
#
# If you don't want to see the assembly instructions mingled in then just look
# at the latest cluster round
# i.e. 'z_cluster.txt'
#
# 13 - 004113D3
# 14 - c1______#11
# 15 - f1_______________#47
# 16 - a21_#2
# 17 - 00411411
# 18 - f1_______________#47
#------------------------------------------------------------------------------

import utils
import os
import sys
import re

#------------------------------------------------------------------------------
# Globals
#------------------------------------------------------------------------------
freq_graph  = []
cluster_lst = []
window      = []
bt_window   = [] # same as window except the key is new cluster
bt_greedy   = []
new_cluster_lst = []
init_greedy_cluster = {}

#------------------------------------------------------------------------------
# Imports
#------------------------------------------------------------------------------

try:
    from collections import defaultdict
except ImportError:
    utils.vd_error("import defaultdict failed")

try:
    from collections import OrderedDict
except ImportError:
    utils.vd_error("import OrderedDict failed")

freq_graph = defaultdict(list)
window     = defaultdict(list)
bt_window  = defaultdict(list)
bt_greedy  = defaultdict(list)


#------------------------------------------------------------------------------
# Add element to window dict table.
#
# cluster   [window size,  new cluster id]
# 401000       [(1,           401000)]
# 401004       [(5,           a12_#5)]
#
# The cluster 'a12_#5' is constructed for breakdown.
#    'a' is a letter of the alphabet that represents the round number
#    '12' is just a number that increases for each unique cluster
#    '_' then adding "_" to show depth (easier to see when looking at clusters)
#    '#5' how big the cluster is.  In this case it is 5 instructions
#
# bt_window[] - bt = backtrace
# It is similar window[] however, the value in window is used
# as a key
# i.e.
# window[]
# 004113D3 - [(1, '4010E0')]
# 004113D5 - [(3, 'a45_#3')]
#
# bt_window[]
# 4010E0  - [(1, '4113D3')]
# a45_#3  - [(3, '4113D5')]
# this makes it easy to has on the cluster when calling backtrace() function
#
# round      = inc number that corresponds to a letter of alphabet
# window_sz  = number that indicates cluster size for a pattern
# cluster_id = cluster id
#------------------------------------------------------------------------------
def add_cluster_id(round, window_sz, cluster_id, isGreedy=False):
    global window
    global bt_window

    # validation check...we only want one entry for our new cluster id
    val = window.get(cluster_id)
    if val is not None:
        # using the greedy alg. we have encountered the id so just return
        # the cluster id
        if isGreedy:
            return val[0][1] # return the cluster id
        else:
            print "<!> must have a unique cluster id ", cluster_id
            utils.vd_error("Internal error - add_cluster_id()")


    add_cluster_id.rollover += 1

    if window_sz > 1:
        add_cluster_id.cluster_id = utils.id_round[round]        +  \
                                    str(add_cluster_id.rollover) +  \
                                    "_#" + str(window_sz)
    else:
        add_cluster_id.cluster_id = cluster_id

    tup = (window_sz, add_cluster_id.cluster_id)
    window[cluster_id].append(tup)

    # bt_window is used for backtrace algorithm
    tup2 = (window_sz, cluster_id)
    bt_window[add_cluster_id.cluster_id].append(tup2)

    return add_cluster_id.cluster_id

add_cluster_id.cluster_id = ""
add_cluster_id.rollover = 0

#------------------------------------------------------------------------------
# Concatenate two cluster_ids.
#------------------------------------------------------------------------------
def cat_2clusters(round, cluster1, cluster2):
    global init_greedy_cluster

    new_cluster = ""

    cat = utils.id_round[round] + "_" + cluster1 + cluster2

    # get total size of cluster
    num = cluster1.find('#')
    if num != -1:
        cluster1_num = cluster1[num+1:]
    else:
        # this is a case of combining a cluster with a virtual address
        cluster1_num = 1
    num = cluster2.find('#')
    if num != -1:
        cluster2_num = cluster2[num+1:]
    else:
        cluster2_num = 1

    # validation check...we only want one entry for our new cluster id
    val = init_greedy_cluster.get(cat)
    if val is not None:
        # using the greedy alg. we have encountered the id so just return
        # the cluster id
        return val

    cat_2clusters.unique_id += 1

    new_cluster += utils.id_round[round] + str(cat_2clusters.unique_id)

    # grow __ according to level
    #while round > 0:
    #    new_cluster += "___"
    #    round -= 1

    sum = int(cluster1_num) + int(cluster2_num)

    # grow __ according to size
    if sum < 50:
        factor = 1
    elif sum >= 50 and sum < 100:
        factor = 4
    elif sum >= 100 and sum < 200:
        factor = 8
    elif sum >= 200 and sum < 400:
        factor = 12
    elif sum >= 400 and sum < 700:
        factor = 18
    elif sum >= 700 and sum < 1000:
        factor = 24
    elif sum >= 1000 and sum < 2000:
        factor = 34
    elif sum >= 2000 and sum < 3000:
        factor = 44
    else:
        factor = 54

    new_cluster += "_" * factor

    # account for number size first. i.e. #7 vs #123 is two chars bigger
    sz = len(str(sum))
    if sz == 1:    # 1 digit
        digit = 3
    elif sz == 2:
        digit = 2
    else:
        digit = 1

    # account for number unique id. i.e. a1 vs a101 is two chars bigger
    sz = len(str(cat_2clusters.unique_id))
    if sz == 1:    # 1 digit
        digit += 3
    elif sz == 2:
        digit += 2
    else:
        digit += 1

    new_cluster += "_" * digit

    new_cluster += "#" + str(sum)

    init_greedy_cluster[cat] = new_cluster

    return new_cluster

cat_2clusters.unique_id  = 0

#------------------------------------------------------------------------------
# This method looks at the cluster list then iterates through this list
# looking for more matches.  Reference the freq graph to see if there is any
# duplicate sequential line matches
# i.e.
# 004113A0
# a_a1_#2 <- a_a1_#2 + a_a2_#3 match - will become b1___#5
# a_a2_#3
# a_a1_#2 <- a_a1_#2 + a_a2_#3 match - will become b1___#5
# a_a2_#3
# a_a1_#2 <- no match, but could be another match for a1,a3
# a_a3_#8
#------------------------------------------------------------------------------
def greedy_new_cluster(round):
    global freq_graph
    global cluster_lst
    global new_cluster_lst
    global bt_greedy
    global init_greedy_cluster

    sys.stdout.write("Create greedy clustering")

    del new_cluster_lst[:]
    bt_greedy.clear()
    init_greedy_cluster.clear()
    cat_2clusters.unique_id  = 0

    prev_cluster = 0
    cur_cluster  = 0
    found_cnt    = 0
    found        = False
    ret          = False

    cluster_len = len(cluster_lst)
    idx = 0

    while cluster_len > idx:

        utils.progress_bar(500)

        # make sure we don't exceed our list
        if cluster_len > idx + 1:
            prev_cluster     = cluster_lst[idx]
            prev_cluster_lst = freq_graph[prev_cluster]
            cur_cluster      = cluster_lst[idx+1]
            cur_cluster_lst  = freq_graph[cur_cluster]
            #print "prev ", idx, prev_cluster
            #print "curr ", idx, cur_cluster
        else:
            break

        # don't cluster system calls - easier to see in the final assembly
        if cur_cluster.find('#') == -1:
           if utils.is_number_hex(cur_cluster) == False:
                new_cluster_lst.append(prev_cluster)
                new_cluster_lst.append(cur_cluster)
                idx += 2
                continue

        # don't cluster system calls - easier to see in the final assembly
        if prev_cluster.find('#') == -1:
           if utils.is_number_hex(prev_cluster) == False:
                new_cluster_lst.append(prev_cluster)
                idx += 1
                continue

        # see if the prev_id's line numbers have any matches
        # now check next line if there is a sequence of line nums
        for linenum in prev_cluster_lst:
            seq_linenum = linenum + 1
            #print "seq_linenum ", seq_linenum

            # see if we can find that value in the next_key
            for current_linenum in cur_cluster_lst:
                if current_linenum == seq_linenum:
                    #print "current_linenum ", current_linenum
                    found_cnt += 1
                    if found_cnt > 1: # we have a cluster!!!
                        new = cat_2clusters(round, prev_cluster,cur_cluster)
                        #print "Found new ", new, prev_cluster, cur_cluster,\
                        #      seq_linenum, found_cnt
                        found_cnt = 0
                        found = True
                        idx += 1
                        break
            if found:
                break

        if found == True:
            new_cluster_lst.append(new)

            # bt_greedy is used for backtrace algorithm
            val = bt_greedy.get(new)
            if val is None:
                tup = (prev_cluster, cur_cluster)
                bt_greedy[new].append(tup)

            ret = True
        # no cluster found, just push it through
        else:
            new_cluster_lst.append(prev_cluster)
            #print prev_cluster, " prev_cluster"

        idx      += 1
        found     = False
        found_cnt = 0

    # print out our last one since we are compair prev and current we need
    # to grab the last one, which is current :)
    if (cluster_len - idx) == 1:
        new_cluster_lst.append(cur_cluster)

    return ret

#------------------------------------------------------------------------------
# The first pass made on a runtrace...we can compress basic blocks that are
# found in a loop
#
# Build a table of window size for each cluster with an cluster id
#
# freq_graph[] - This table is needed to help me build window[]
# 4113D5 - [44, 77, 110, 143] <--- windows size is computed at 3 for 40113D5
# 4113D8 - [45, 78, 111, 144]      A basic block
# 4113DB - [46, 79, 112, 145]
# 4113DE - [14, 47, 80,  118, 151] <--- A new basic block
#
# This method is used only once as a quick way to compress basic blocks found
# in loops...
# As you can see from the structure, we have a new basic block at
# 0x4113DE...This frequency graph is built from sample_loop_exe.exe.
# If you disassemble this file and go to address 0x411ED5 you will see it is a
# destination address or beginning of a basic block.  Now you also see that
# in that basic block contains 0x4113D8 and 0x4113DB.  Now so long as this
# basic block has sequential line numbers and the same count of line numbers
# then we can compress the entire basic block into a cluster a16_#3.
#
# window[] - This table is created to keep track of window size and cluster id
# for each round
#  cluster   [window size,   new cluster id]
# 4113A1   - [(1,           4113A1)]
# 4113A3   - [(1,           4113A3)]
#  ....
# 4113D3   - [(1,           4113D3)]
# 4113D5   - [(3,           A16_#3)]  <--- our new cluster with size 3
#------------------------------------------------------------------------------
def compress_basic_blocks_loop(round):
    global freq_graph
    global window
    global bt_window  # this table is for reversing the process

    bt_window.clear()

    sys.stdout.write("Compressing basic blocks")

    sorted_dict = OrderedDict(sorted(freq_graph.iteritems()))

    found_cnt = 0
    idx       = 0
    temp_lst  = []
    check_next_cluster = False

    cluster_len = len(sorted_dict)
    while cluster_len > idx:

        utils.progress_bar(500)

        # make sure we don't exceed our list
        if cluster_len > idx + 1:

            prev_cluster        = sorted_dict.keys()[idx]
            prev_cluster_lst    = freq_graph[prev_cluster]
            cur_cluster         = sorted_dict.keys()[idx+1]
            cur_cluster_lst     = freq_graph[cur_cluster]
            #print "\nprev ", idx, prev_cluster
            #print "curr ", idx + 1, cur_cluster
        else:
            break

        curr_num_elmts = len(cur_cluster_lst)
        prev_num_elmts = len(prev_cluster_lst)
        last_cluster = prev_cluster

        # an instruction that only happens once or we have a symbol name
        # in the case of the symbol name we will let greedy clustering handle
        if prev_num_elmts == 1 or utils.is_number_hex(last_cluster) == False:
            new = add_cluster_id(round, 1, last_cluster)
            idx += 1
            continue

        # compress lines
        if curr_num_elmts == prev_num_elmts:
            #print "lets compare"

            for prev_idx, prev_val in enumerate(prev_cluster_lst):
                seq_val = prev_val + 1

                cur_val = cur_cluster_lst[prev_idx]

                # do the values match after adding one?
                if cur_val == seq_val:
                    found_cnt += 1
                else:
                    #print "no dice...cur_val != seq_val"
                    check_next_cluster = False
                    found_cnt = 0
                    break

            # search is complete...see if all items are off by only one
            if found_cnt == curr_num_elmts: # cluster
                found_cnt = 0

                # just move up one to see if the next line also can
                # be part of this cluster
                temp_lst.append(last_cluster)
                #print temp_lst
                idx += 1
                check_next_cluster = True
            # if we have 2 lines with same number of elemnts but they don't
            # match (seq_val != cur_val)
            else:
                check_next_cluster = False
        # This line is larger or smaller than the prev line...see if we have
        # any clusters
        else:
            #print "curr_num_elmts != prev_num_elmts"
            if check_next_cluster:
                window_sz = len(temp_lst)
                window_sz += 1  # to account for the last cluster we analyzed
                new = add_cluster_id(round, window_sz, temp_lst[0])
                #print new, window_sz, temp_lst[0], " New Cluster - next line miss match"
                del temp_lst[:] # done tracking clear it
            else:
                #print "better do something: ", cur_cluster, last_cluster
                # no prev line match or seq line match...i.e.
                #411414 - [43, 76, 109, 142]  <------ This guy
                #411416 - [148]
                new = add_cluster_id(round, 1, last_cluster)

            check_next_cluster = False

            idx += 1  # just go to the next cluster
            continue

        # if we have the same
        if check_next_cluster:
            #print "keep searching"
            continue
        else:
            # done looking for our cluster, lets see if we got a winner
            window_sz = len(temp_lst)
            if window_sz > 0:
                window_sz += 1  # to account for the last cluster we analyzed
                new = add_cluster_id(round, window_sz, temp_lst[0])
                #print new, last_cluster, " New Cluster"

                del temp_lst[:] # done tracking clear it
            # They are the same len however they are not seq.
            # 5C93BBBF - [3999, 5031] <---- add this guy
            # 5C93BBC4 - [4042, 5074]
            else:
                new = add_cluster_id(round, 1, prev_cluster)

        idx += 1



    # print out our last one since we are compair prev and current we need
    # to grab the last one, which is current :)
    if (cluster_len - idx) == 1:
        new = add_cluster_id(round, 1, cur_cluster)

    add_cluster_id.cluster_id = ""
    add_cluster_id.rollover = 0


#------------------------------------------------------------------------------
# This just creates our our reduced cluster after compressing basic blocks to
# our data structure new_cluster_lst[]
#
# NOTE: you must create the window, and cluster_lst before calling this func
# a1_#1
# ...
# a23_#5  <- a23_#5 represents 5 instructions
# a24_#1
# ...
#------------------------------------------------------------------------------
def compress_create_new_cluster(round):
    global window
    global cluster_lst
    global new_cluster_lst

    del new_cluster_lst[:]

    print "Create clustering..."

    line_num = len(cluster_lst)
    idx = 0

    while line_num > idx:

        try:
            id = cluster_lst[idx]

            #print idx, id

            #           ID    cluster size      id
            # window - 401000 -   [(2,       'a12_#2')]
            win_val    = window[id]
            win_lst    = win_val[0]
            win_sz     = win_lst[0]
            cluster_id = win_lst[1]

            new_cluster_lst.append(cluster_id)

            # skip over line_num instructions that are part of the cluster since
            # that key will not be located in the window
            idx += win_sz
        except:
            print "id, idx: ", id, idx
            utils.vd_error("idx out of range - compress_create_new_cluster()")



#------------------------------------------------------------------------------
# Read in a cluster list then build a freq table
#------------------------------------------------------------------------------
def build_freq_graph(round):
    global cluster_lst
    global freq_graph

    freq_graph.clear()

    cluster_name = utils.id_round[round] + "_" + "cluster"  + ".txt"

    print "\nBuilding frequency graph from: [" + cluster_name + "]"

    for linenum, cluster in enumerate(cluster_lst):
        add_freq(cluster, linenum)

#------------------------------------------------------------------------------
# Read backtrace files "round_backtrace.txt"
#------------------------------------------------------------------------------
def read_backtrace(isAll, isHashed, round):

    bt = []

    if isHashed == True:
        bt = defaultdict(list)

    if isAll:
        cluster_name = utils.BT_ALL_FILE
    else:
        cluster_name = utils.id_round[round] + "_backtrace.txt"

    print "- reading backtrace file: " + cluster_name

    try:
        ifile = open(cluster_name, "r")
    except IOError as exc:
        raise IOError("%s: %s" % (cluster_name, exc.strerror))

    while 1:
        line = ifile.readline()
        if len(line) == 0:
            break

        line = line.strip("\n")
        cluster_line = line.strip().split()

        cluster_id = cluster_line[0]
        lst = cluster_line[1:]

        if isHashed == True:
            val = bt.get(cluster_id)

            # if key does not exist then add it
            if val is None:
                for x, linenum in enumerate(lst):
                        bt[cluster_id].append(linenum)
        else:
            item = (cluster_id, lst)
            bt.append(item)

    ifile.close()

    return bt

#------------------------------------------------------------------------------
# Loop through all backtrace files to reconstruct the original runtrace
# Those files are identified by round_backtrace.txt
# ie. a_backtrace.txt, b_backtrace.txt....
#
# To validate if this function worked, call function validate_backtrace_all()
#------------------------------------------------------------------------------
def backtrace_all(round):

    prev_bt     = []
    tbl_name    = ""
    isAll       = False

    found = False

    if os.path.exists(utils.BT_ALL_FILE):
        isAll = True

    prev_round = round

    # if the "all_backtrace.txt" exists then read from it, otherwise
    # read from the last round_backtrace.txt that was created
    # The idea is to keep rewriting "all_backtrace.txt" as we recursively
    # loop through all the round_backtrace.txt files
    isHashed = False
    bt = read_backtrace(isAll, isHashed, round)

    # now we can overwrite all_backtrace.txt with a new round
    tbl_name = utils.BT_ALL_FILE
    try:
        ofile = open(tbl_name, "w")
    except IOError as exc:
        raise IOError("%s: %s" % (tbl_name, exc.strerror))

    str_out     = ""
    prev_round -= 1
    isHashed    = True

    prev_bt = read_backtrace(False, isHashed, prev_round)

    # substitue items in the most recent backtrace with those of prev
    # backtrace files "round_backtrace.txt"
    for current_line in bt:
        current_key = current_line[0]
        current_val = current_line[1:]

        str_out += current_key + " "

        for lst_val in current_val:
            for x in lst_val:

                # lookup the previous backtrace cluster and copy its contents
                # to the parent cluster.
                expanded_key = prev_bt[x]

                # if the val does not exist then just treat the value as the
                # key and pass it through.  Happens when unfolding.  The
                # previous backtrace will not contain the key that we unfolded
                if len(expanded_key) == 0:
                    str_out += x + " "
                    #print "HERE", x
                    continue

                for t in expanded_key:
                    str_out += t + " "

            str_out += "\n"

    print "- writing " + tbl_name
    ofile.writelines(str_out)

    ofile.close()

#------------------------------------------------------------------------------
# Rebuild the instruction trace from our clustering files using greedy
# bt_greedy[] that was populated in greedy_new_cluster()
# I use this function instead of backtrace() b/c I use  bt_greedy[]
# Input format of bt_greedy[]
# new cluster    cluster    cluster
# b1___#7    - [('a16_#2', 'a17_#5')]
# b2___#4    - [('a19_#2', 'a20_#2')]
#
# Note: output format looks like
# i.e.
# ...
# 004113D3 004113D3
# b1___#7 a16_#2 a17_#5
# b2___#4 a19_#2 a20_#2
# ...
#------------------------------------------------------------------------------
def greedy_backtrace(round, print_screen):
    global bt_greedy
    global cluster_lst

    print "Greedy backtrace - Verification of new cluster "

    if print_screen == False:
        name = utils.id_round[round] + "_backtrace.txt"
        try:
            ofile = open(name, "w")
        except IOError as exc:
            raise IOError("%s: %s" % (name, exc.strerror))

    # now look up the cluster id in bt_window
    for cluster in cluster_lst:
        val = bt_greedy.get(cluster)
        if val is None:
            # no key for item so it is unique.  Just print it out
            str_out = cluster + " " + cluster
            if print_screen:
                print str_out
            else:
                str_out += "\n"
                ofile.writelines(str_out)
            continue

        lst = bt_greedy[cluster]
        tup = lst[0]
        prev_cluster    = tup[0]
        cur_cluster = tup[1]
        str_out = cluster + " " + prev_cluster + " " + cur_cluster
        if print_screen:
            print str_out
        else:
            str_out += "\n"
            ofile.writelines(str_out)

    if print_screen == False:
        print "   - " + name
        ofile.close()

#------------------------------------------------------------------------------
# Rebuild the instruction trace from our clustering files after compression of
# basic blocks
#
# For BackTrace
# 1: BT_WINDOW
# Generates new cluster id's and associated window sz...so I can search based
# off of a key, then I need to make the new cluster id the key...inverse of
# WINDOW
#     new cluster   window size  old cluster id
#       a14_#3     - [(3,         004113D5)]
#       a15_#2     - [(2,         004113DE)]
# Once I have the "new cluster id" I can check the freq_graph key
# (old cluster id) to find out what what line number it is located on in the
# LINE_LST.  Given that I have the window size then we can extract the exact
# sequence of id's
#
# Note: Examples for the win!
# i.e. - Format looks like
# a15_#2 4113DE 4113E2
# a16_#5 4113E4 4113E7 4113EA 4113ED 4113F4
#------------------------------------------------------------------------------
def compress_backtrace(round, print_screen):
    global bt_window
    global freq_graph
    global cluster_lst
    global new_cluster_lst

    print "Backtrace - Verification of new cluster "

    if print_screen == False:
        tbl_name = utils.id_round[round] + "_backtrace.txt"
        try:
            ofile = open(tbl_name, "w")
        except IOError as exc:
            raise IOError("%s: %s" % (tbl_name, exc.strerror))

    # now look up the cluster id in bt_window
    for new_cluster in new_cluster_lst:
        lst = bt_window[new_cluster]
        tup = lst[0]
        win_sz = tup[0]
        old_cluster = tup[1]
        if win_sz == 1:
            str_out = new_cluster + " " + old_cluster
        # now we have a window size that is larger than one which means we have
        # multiple cluster ids (eventually translates to instructions).
        # look into freq_graph to get a line number...this line number we will
        # use to look into LINE_LST to get our cluster id's to expand on
        # a cluster id
        else:
            lst = freq_graph[old_cluster]
            line_num = lst[0]

            str_out = new_cluster + " "

            idx = 0
            cnt = 0

            while win_sz > 0:
                idx = cnt + int(line_num)

                cluster = cluster_lst[idx]

                str_out += cluster + " "

                win_sz -= 1
                cnt += 1

        if print_screen == True:
            print str_out
        else:
            str_out += "\n"
            ofile.writelines(str_out)

    if print_screen == False:
        print "   - " + tbl_name
        ofile.close()


#------------------------------------------------------------------------------
# Print out a internal table either to file or screen
#------------------------------------------------------------------------------
def print_tbl(round, tbl, tbl_type, print_screen, out_type, nested):

    if round != -1:
        tbl_name = utils.id_round[round] + "_" + tbl_type + ".txt"
    else:
        tbl_name = "orig_" + tbl_type + ".txt"

    if nested:
        if print_screen:
            prefix_str = "- printing: " + tbl_name
        else:
            prefix_str = "   - " + tbl_name
    else:
        if print_screen:
            prefix_str = "Printing: " + tbl_name
        else:
            prefix_str = "   - " + tbl_name

    print prefix_str

    if print_screen == False:
        try:
            ofile = open(tbl_name, "w")
        except IOError as exc:
            raise IOError("%s: %s" % (tbl_name, exc.strerror))

    cnt = 0

    if out_type == utils.DEFAULT_DICT:
        for k,v in tbl.iteritems():
            out_str = str(k) + " - " + str(v)
            if print_screen:
                print out_str
            else:
                out_str += "\n"
                ofile.writelines(out_str)
    elif out_type == utils.LIST:
        for i in tbl:
            out_str = str(cnt) + " - " + i
            if print_screen:
                print out_str
            else:
                out_str += "\n"
                ofile.writelines(out_str)
            cnt += 1

    if print_screen == False:
        ofile.close()

#------------------------------------------------------------------------------
# Print window size table
#------------------------------------------------------------------------------
def print_compress_window(round, print_screen):
    global window

    if print_screen:
        print "\nPrinting window/new cluster table"
    else:
        print "\nWriting window/new cluster table"

    sorted_dict = OrderedDict(sorted(window.iteritems()))

    print_tbl(round, sorted_dict, "window_sz", print_screen,
              utils.DEFAULT_DICT, True)

#------------------------------------------------------------------------------
# Print backtrace window table
# I use print_compress_backtrace as a way to create a hash to allow me to
# create a backtrace
# It is similar window[] however, the value in window is used
# as a key
# i.e.
# window[]
# 004113D5 - [(3, 'a14_#3')]
# 004113DE - [(2, 'a15_#2')]
#
# bt_window[]
# 004113D5 - [(3, 'a14_#3')]
# 004113DE - [(2, 'a15_#2')]
# this makes it easy to hash on the cluster when calling backtrace() function
#------------------------------------------------------------------------------
def print_compress_backtrace(round, print_screen):
    global bt_window

    if print_screen:
        print "Printing compression backtrace "
    else:
        print "Writing compression backtrace "

    sorted_dict = OrderedDict(sorted(bt_window.iteritems()))

    print_tbl(round, sorted_dict, "bt_win_sz", print_screen,
              utils.DEFAULT_DICT, True)

#------------------------------------------------------------------------------
# Print greedy backtrace
#------------------------------------------------------------------------------
def print_greedy_backtrace(round, print_screen):
    global bt_greedy

    if print_screen:
        print "Printing greedy backtrace "
    else:
        print "Writing greedy backtrace "

    sorted_dict = OrderedDict(sorted(bt_greedy.iteritems()))

    print_tbl(round, sorted_dict, "bt_greedy", print_screen,
              utils.DEFAULT_DICT, True)

#------------------------------------------------------------------------------
# Print frequency dict
#------------------------------------------------------------------------------
def print_freq_graph(round, print_screen):
    global freq_graph

    if print_screen:
        print "Printing frequency graph "
    else:
        print "Writing frequency graph "

    # freq_graph = OrderedDict(sorted(freq_graph.iteritems()))
    # I tried this and it causes a 'KeyError'
    # I don't want to assign the OrderedDict sorted to freq_graph b/c it
    # changes the freq_graph from defaultdict to an OrderedDict with will screw
    # up using that list in the future
    sorted_dict = OrderedDict(sorted(freq_graph.iteritems()))

    print_tbl(round, sorted_dict, "freq", print_screen, utils.DEFAULT_DICT,
              True)

#------------------------------------------------------------------------------
# Used to validate clusters - func creates 'validate.txt' file
# The output of this file can be compared to the orig_cluster.txt to validate
# the clusters were correctly assembled.
# i.e.
# diff validate.txt orig_cluster.txt
#------------------------------------------------------------------------------
def validate_backtrace_all(print_screen):

    if print_screen:
        print "Printing backtrace for validation "
    else:
        print "Writing backtrace for validation: " + utils.VALIDATE_FILE

    bt      = []
    cnt     = 0
    str_out = ""
    cluster_name = utils.BT_ALL_FILE

    sys.stdout.write("- reading backtrace file: " + cluster_name)

    # open file to write out to screen or file
    try:
        ifile = open(cluster_name, "r")
    except IOError as exc:
        raise IOError("%s: %s" % (cluster_name, exc.strerror))

    # open validate.txt file to write to file
    if print_screen == False:
        try:
            ofile = open(utils.VALIDATE_FILE, "w")
        except IOError as exc:
            raise IOError("%s: %s" % (cluster_name, exc.strerror))

    while 1:

        utils.progress_bar(500)

        line = ifile.readline()
        if len(line) == 0:
            break

        line = line.strip("\n")
        cluster_line = line.strip().split()

        cluster_id = cluster_line[0]
        lst = cluster_line[1:]

        for x, linenum in enumerate(lst):
            str_out = str(cnt) + " - " + linenum
            if print_screen == True:
                print str_out
            else:
                str_out += "\n"
                ofile.writelines(str_out)
            cnt += 1

    if print_screen == False:
        ifile.close()
        ofile.close()

#------------------------------------------------------------------------------
# Print our new cluster list
#------------------------------------------------------------------------------
def print_cluster(round, print_screen):
    global cluster_lst

    if print_screen:
        print "\n* Printing new cluster "
    else:
        print "\n* Writing new cluster "

    print_tbl(round, cluster_lst, "cluster", print_screen, utils.LIST, True)

#------------------------------------------------------------------------------
# Cluster virtual addresses by their line numbers
#
# freq_graph[]
# cluster   line numbers
# 4113D3    - [13]
# 4113D5    - [44, 77, 115, 148]
# 4113D8    - [45, 78, 116, 149]
# 4113DB    - [46, 79, 117, 150]
# 4113DE    - [14, 47, 80, 118, 151]
#------------------------------------------------------------------------------
def add_freq(id, line_num):
    global freq_graph
    global cluster_lst

    #print line_num, id

    freq_graph[id].append(line_num)

#------------------------------------------------------------------------------
# The greedy clustering algorithm will create a cluster if it finds a match
# in the freq_graph.  However, another cluster can be created further down
# the cluster list and create yet another cluster.  If this happens then we
# can have single clusters.  I choose to expand these single cluster.  However,
# you don't have to...it is still correct output.  Just comment out this
# functions if you want it tighter.  Here is an example of this happening:
#
# A
# B  ---- cluster c1_#2 created - contains [A, B]+ this guy will be unfolded
# 401000
# A  ---- cluster c2_#2 created - contains [401000, A]
# B
# 401000
# A  ---- cluster c2_#2 created - contains [401000, A]
# C
#------------------------------------------------------------------------------
def unfold_single_clusters(round):
    global new_cluster_lst
    global freq_graph
    global bt_greedy

    unfolded_cluster_lst = []
    found = False

    print "\nUnfold single clusters\n"

    for cluster in new_cluster_lst:
      if utils.is_number_hex(cluster):
         unfolded_cluster_lst.append(cluster)
      else:
        if cluster.find('#') != -1:  # make sure it is a cluster
            linenums = freq_graph[cluster]
            if len(linenums) == 1:
                cluster_round = cluster[:1]

                # open the backtrace file for that round and find the items
                # that make up the cluster
                cluster_name = cluster_round + "_backtrace.txt"

                try:
                    ifile = open(cluster_name, "r")
                except IOError as exc:
                    raise IOError("%s: %s" % (cluster_name, exc.strerror))

                while 1:
                    line = ifile.readline()
                    if len(line) == 0:
                        break

                    line = line.strip("\n")
                    cluster_line = line.strip().split()

                    cluster_id = cluster_line[0]
                    lst = cluster_line[1:]

                    # find our single cluster, and unfold it
                    if cluster_id == cluster:
                        found = True
                        print "<<<< unfolded cluster:", cluster_id, lst
                        for x in lst:
                            unfolded_cluster_lst.append(x)

                        break

                ifile.close()
            # cluster just pass it through
            else:
                unfolded_cluster_lst.append(cluster)
        # cluster just pass it through
        else:
            unfolded_cluster_lst.append(cluster)

    new_cluster_lst = unfolded_cluster_lst[:]

    if found:
        print_tbl(round, unfolded_cluster_lst, "cluster", False, utils.LIST,
                  True)
    else:
        print "   - no more unfolding"

    return found

#------------------------------------------------------------------------------
# Format an run trace instruction from our database
#------------------------------------------------------------------------------
def format_ins_trace(va, mnem, thread, regs, dbgr):

    # Olly 2.0
    if dbgr == utils.OLLY:
        if regs == "None":
            out_s = va + " " + mnem + "\n"
        else:
            out_s = va + " " +  mnem.ljust(30) + ";" + regs + "\n"

    # Immunity and Olly 1.10
    elif dbgr == utils.IMMUNITY:
        if thread == "Unknown":
            thread = ""
        if regs == "None":
            out_s = va + " " + mnem + "\n"
        else:
            out_s = va + " " +  mnem.ljust(30) + regs + "\n"

    # WinDbg
    elif dbgr == utils.WINDBG:
        out_s = va + " " + mnem.ljust(30) + "  " + thread + "\n"
    else:
        utils.vd_error("Make sure to declare a debugger -d switch")

    return out_s

#------------------------------------------------------------------------------
# Format a run trace instruction to be assembled by NASM
#------------------------------------------------------------------------------
def format_ins_asm(ins, thread, regs, dbgr):
    leading_spaces = "    "
    out_s = ""
    sys_var = ""

    ins_lst = ins.strip()

    # split by , space [ ] or + so we can get to all numbers
    # e.g. cmp dword [edx+7c],0 -> ['cmp', 'dword', 'edx', '7c', '0']
    ins_lst = re.split(',|\[|\]|\-|\+|\.| ', ins_lst)

    # tack a '0x' at the beginning of all numbers
    for item in ins_lst[1:]:  # skip the mnem
        if utils.is_number_hex(item) == True and int(item, 16) > 9:
            new_val = '0x' + item
            ins = ins.replace(item, new_val, 1)
        # sigh...stupid mem symbol name used in operands.  Don't know
        # what the value is so, just replace it with dead
        # MOV EDX,DWORD PTR DS:[EAX*4+__pioinfo]
        elif item.find("__") != -1:
            sys_var = item
            ins = ins.replace(item, "0xDEAD")

    if sys_var:
        ins += "; 0XDEAD swapped with (" + sys_var + ")"
        sys_var = ""

    mnem = ins_lst[0]

    # remove Jxx, CALL, RETs
    if mnem.find('JMP')  != -1 or mnem.find('JE')   != -1 or \
       mnem.find('JO')   != -1 or mnem.find('JNO')  != -1 or \
       mnem.find('JB')   != -1 or mnem.find('JNAE') != -1 or \
       mnem.find('JC')   != -1 or mnem.find('JNB')  != -1 or \
       mnem.find('JAE')  != -1 or mnem.find('JNC')  != -1 or \
       mnem.find('JZ')   != -1 or mnem.find('JNZ')  != -1 or \
       mnem.find('JNE')  != -1 or mnem.find('JBE')  != -1 or \
       mnem.find('JNA')  != -1 or mnem.find('JNBE') != -1 or \
       mnem.find('JA')   != -1 or mnem.find('JS')   != -1 or \
       mnem.find('JNS')  != -1 or mnem.find('JP')   != -1 or \
       mnem.find('JPE')  != -1 or mnem.find('JNP')  != -1 or \
       mnem.find('JPO')  != -1 or mnem.find('JL')   != -1 or \
       mnem.find('JNGE') != -1 or mnem.find('JNL')  != -1 or \
       mnem.find('JGE')  != -1 or mnem.find('JLE')  != -1 or \
       mnem.find('JNG')  != -1 or mnem.find('JNLE') != -1 or \
       mnem.find('JG')   != -1                            or \
       mnem.find('CALL') != -1 or mnem.find('RET')  != -1:
            return out_s

    # NASM does not support
    # LODS, MOVS, STOS, SCAS, CMPS, INS, or OUTS
    # but only supports the forms such as LODSB, MOVSW, and SCASD
    if mnem.find('LODS') != -1:
        ins = get_mnem_based_sz(mnem, ins)
    elif mnem.find('MOVS') != -1:
        ins = get_mnem_based_sz(mnem, ins)
    elif mnem.find('STOS') != -1:
        ins = get_mnem_based_sz(mnem, ins)
    elif mnem.find('INS') != -1:
        ins = get_mnem_based_sz(mnem, ins)
    elif mnem.find('OUTS') != -1:
        ins = get_mnem_based_sz(mnem, ins)
    elif mnem.find('BSWAP') != -1:
        if ins.find('E') == -1:
            op = ins.split(' ', 1)
            ins = mnem + " E" + op[1]  + "; incorrect register gen by Olly " \
                                       + "probably to invoke exception"
    # remove offset and replace either with absolute since it is memory
    elif ins.find('OFFSET') != -1:
        pos = ins.find('OFFSET')
        if utils.is_number_hex(ins[pos+7:]):
            # 7 is to account for the word OFFSET and a space
            ins = ins.replace('OFFSET', '')
        else:
            ins = ins.replace('OFFSET', '0xAAAAAAAA  ; swapped with: offset ')
    else:
        # remove keywords such as PTR, OFFSET, SS:, ..
        ins = ins.replace('PTR', '')
        ins = ins.replace('SS:', '')
        ins = ins.replace('DS:', '')
        ins = ins.replace('FS:[', '[FS:')

        try:
            first_char = mnem[0]
        except:
            utils.vd_error("idx out of range - format_ins_asm()")

        if first_char == 'F':
            # NASM uses different names to refer to floatingpoint registers from
            # OLLY: where olly would call them ST(0), ST(1) and so on, and x86
            # would call them simply 0, 1 and so on, NASM chooses to call them
            # st0, st1 etc.
            operands = ins.split(' ', 1)

            ins = mnem + " " + utils.replace_all(operands[1], utils.ST_REG)

    # Olly 2.0
    if dbgr == utils.OLLY:
        if regs == "None":
            out_s = leading_spaces + ins + "\n"
        else:
            out_s = leading_spaces + ins.ljust(30) + ";" + regs + "\n"

    # Immunity and Olly 1.10
    elif dbgr == utils.IMMUNITY:
        # special case for immunity
        # 636BBC56 Main  PUSH MSVCR90D.636F60B0
        pos = ins.find(".")
        if pos != -1:
            ins = mnem + " " + ins[pos+1:]

        # LEA EAX,DWORD PTR DS:[EDI+EAX*4]  get rid of DWORD as NASM complains
        # of a mismatch in operand size
        if mnem == 'LEA':
           ins = ins.replace('DWORD', '')

        if thread == "Unknown":
            thread = ""
        if regs == "None":
            out_s = leading_spaces + ins + "\n"
        else:
            out_s = leading_spaces + ins.ljust(30) + regs + "\n"

    # WinDbg
    elif dbgr == utils.WINDBG:
        out_s = leading_spaces + ins + "\n"
    else:
        utils.vd_error("Make sure to declare a debugger -d switch")

    return out_s

#------------------------------------------------------------------------------
#------------------------------------------------------------------------------
def get_mnem_based_sz(mnem, ins):
    if ins.find('BYTE') != -1:
        mnem = mnem + "B"
    elif ins.find('DWORD') != -1:
        mnem = mnem + "D"
    elif ins.find('WORD') != -1:
        mnem = mnem + "W"

    return mnem

#------------------------------------------------------------------------------
# Final assembly - All lines that are single items, grab the assembly ins from
# vd.xml and insert into 'final_assembly.txt'
#
# k2____________________________________#3265     [15, 990] 15 (5807)
# e32___________#101                              [16, 224] 16 (9072)
# e56________#76                                               (9173)
# e57___________#101                                           (9249)
# f34___________#173       IP in smaller clusters [19, 205] 19 (9350)
# g18_______________#343                          [20, 35] 20  (9523)
# f37___________#173                                           (9866)
# f38___________#179                                           (10039)
# e64________#79                                               (10218)
# k3________________________________#2919         [24, 47] 24  (10297)
#
# k2___#3265 cluster that is huge and is a context restore/transition
#            of the virtual machine
# k3___#2919 restore context for the application to make a system call (printf)
#
# So what is the [] and () mean?
#
# [15, 990] 15 (5807)
#   |        |    |
#   |        |    ----------> runtrace line number
#   |        |
#   |        ---------------> current file line number of final_assembly.txt
#   |
#   ------------------------> line numbers of where this cluster is duplicated on
#
# - [15, 990] tells the reverser that this cluster (k2), is located in file
#   final_assembly.txt at line numbers 15 and 990.
# - 15 current file line number
# - (5807) tells the reverser what line number in the runtrace this cluster
#          begins
#------------------------------------------------------------------------------
def final_assembly(round, etree, dbgr):
    global new_cluster_lst
    global freq_graph

    out_s = ""

    print "\n"
    print "_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_"
    sys.stdout.write("Final assembly - final_assembly.txt")

    ofile_name = "final_assembly.txt"
    ofile = open(ofile_name, "w")

    thread   = ""
    va       = ""
    mnem     = ""
    regs     = ""
    line_num = 0
    run_trace_offset = 1
    total_ins = 0
    cluster_total = 0

    len_cluster_lst = len(new_cluster_lst) - 1

    tree = etree.iterparse('vd.xml', events=('end',))

    found = False
    line = -1
    for action, elem in tree:

        if elem.text is not None:
            if elem.tag == 'thread':
                thread = elem.text
            elif elem.tag == 'va':
                va = elem.text

                # find single ins
                va_item = new_cluster_lst[line+1]
                if va == va_item:
                    found = True
                    total_ins += 1
                    line += 1

            elif elem.tag == 'mnem' and found:
                mnem = elem.text
            elif elem.tag == 'regs' and found:
                regs = elem.text
                out_s = format_ins_trace(va, mnem, thread, regs, dbgr)
            elif elem.tag == 'ins' and found:
                line_num = elem.text

                # account for all ins that are not clusters
                run_trace_offset += total_ins
                total_ins = 0

                ofile.writelines(out_s)
                found = False

                # print out all non-hex values (clusters!)
                next_item = line
                while True:
                    if len_cluster_lst > next_item + 1:
                        next_item += 1
                        try:
                            item = new_cluster_lst[next_item]
                        except:
                            print "next_item: ", next_item
                            utils.vd_error("idx out of range-final_assembly()")

                        # system calls - make a divider to easily see the
                        # break of system calls
                        if item.find('#') == -1:
                           if utils.is_number_hex(item) == False:
                                #ofile.writelines(utils.divider)

                                total = "++++++++++++++++++++++ " + \
                                        "(ins total: " + \
                                        str(cluster_total) + ")" + \
                                        " ++++++++++++++++++++++ " + "SYSCALL: "
                                cluster_total = 0

                                ofile.writelines(total)
                               # ofile.writelines(utils.divider)

                        # Look for cluster____#num
                        if item.find('#') != -1:
                            line += 1

                            # add what lines this cluster is located at
                            cluster = str(item)
                            val = freq_graph.get(cluster)
                            if val is not None:
                                if len(val) > 1:
                                    # add 1 to items since we start at 0 idx
                                    temp = [x + 1 for x in val]
                                    lines = str(temp) + " " + str(line + 1)
                                else:
                                    lines = ""


                            clus_out = cluster.ljust(80) + lines + " (" + \
                                       str(run_trace_offset) + ")"
                            ofile.writelines(clus_out + "\n")

                            # calculate the offset in the runtrace
                            num = item.find('#')
                            run_trace_offset += int(item[num+1:])

                            # keep a total until syscall break
                            num = item.find('#')
                            cluster_total += int(item[num+1:])

                        else:
                            break
                    else:
                        break

            utils.progress_bar(5000)

            # eliminate empty refs from root node
            elem.clear()
            while elem.getprevious() is not None:
                del elem.getparent()[0]


    ofile.close()

#------------------------------------------------------------------------------
# Break clusters into files, then populate them with the runtrace instructions
# that make up the cluster.
#
# By default, VD creates a dir called "chunk_cluster" that creates clusters
# with the correct runtrace assembly ins.
#
# Example:
# Look at final_assembly.txt on any cluster line...say "f34___________#173"
# then go into the dir "chunk_cluster" and open the corresponding file.
# (Keep in mind that clusters can have multiple files, so I name the file by
# the cluster name plus the line number in final_assembly.txt file
# e.g.
# f34___________#173_19.txt
#                     |
#                     ------------> file line number
#
# Once you open this file you will see that there is 173 instructions and
# all the correct register effects.
#------------------------------------------------------------------------------
def chunking_clusters(etree, dbgr):
    global new_cluster_lst
    global freq_graph

    out_s = ""

    sys.stdout.write("\nChunking Clusters\n")

    chunk_dir = "chunk_cluster"
    if not os.path.exists(chunk_dir):
        os.makedirs(chunk_dir)

    thread   = ""
    va       = ""
    mnem     = ""
    regs     = ""

    line      = 0
    db_idx    = 0
    ins_total = 0
    offset    = 0

    tree = etree.iterparse('vd.xml', events=('end',))

    # Look for cluster____#num
    for cluster in new_cluster_lst:
        if cluster.find('#') != -1:

            #print "\n\n", cluster, "\n\n"

            finalasm_align = line + 1 # final asm line nums are inc by 1

            # open cluster file name with line number appended
            ofile_name = '%s_%s.asm' % (cluster, finalasm_align)
            ofile_path = os.path.join(chunk_dir, ofile_name)
            ofile = open(ofile_path, "w")

            # grab the number of ins in cluster
            num = cluster.find('#')
            ins_num = int(cluster[num+1:])

            #print "ins_total  line  ins_num", ins_total, line, ins_num
            # end of range for ins for a cluster
            # -1 is accounting the the cluster name itself
            ins_total += line + ins_num - 1
            #print "ins_total += ", ins_total

            find_first_ins_cluster = True

            # print out instructions from database
            for action, elem in tree:
                if elem.text is not None:
                    if elem.tag == 'thread':
                        thread = elem.text
                    elif elem.tag == 'va':
                        va = elem.text
                        #print db_idx, va
                    elif elem.tag == 'mnem':
                        mnem = elem.text
                    elif elem.tag == 'regs':
                        regs = elem.text
                        out_s = format_ins_trace(va, mnem, thread, regs, dbgr)
                    elif elem.tag == 'ins':
                        # find first ins in database for cluster
                        # basically skip single ins in cluster file (not DB)
                        # e.g. - new_cluster_lst[]
                        # 20 - a21_#2
                        # 21 - 00411411     <---------- skip this guy
                        # 22 - f1______#47
                        if db_idx != offset and find_first_ins_cluster == True:
                            #print "skip single ins ", va
                            db_idx += 1
                            continue

                        find_first_ins_cluster = False

                        line_num = elem.text
                        ofile.writelines(out_s)

                        if db_idx == ins_total:
                            #print "close file...db_idx, ins_total ", db_idx, ins_total
                            ofile.close()
                            find_first_ins_cluster = True
                            ins_total -= line
                            db_idx += 1
                            offset = db_idx
                            break

                        db_idx += 1

                    utils.progress_bar(5000)

                    # eliminate empty refs from root node
                    elem.clear()
                    while elem.getprevious() is not None:
                        del elem.getparent()[0]

        # non-cluster - VA
        else:
            offset += 1
            #print "non-cluster - db_idx, offset ", db_idx, offset

        line += 1

#------------------------------------------------------------------------------
# Create sections based off a size limit on clusters. (option -s)
# If you want to pull the runtrace for a certain range (defined by cluster size)
# e.g. If you set the limit to 47 this alg will:
# 1 - create a dir called ../chunk_sections/
# 2 - generate files based off line number in final_assembly.txt (22.txt)
# 3 - 22.txt will contain all instructions in a21_#2 to f1_____#47
# 004113D3 JMP SHORT 004113DE
# f1______#47
# a21_#2                    <----- section starts here
# c2_______#8
# a21_#2
# 00411411 MOV EAX,DEADBEEF <----- section ends here
# f1______#47
#------------------------------------------------------------------------------
def chunking_sections(etree, dbgr, section_sz):
    global new_cluster_lst

    section = []
    section = defaultdict(list)
    out_s = ""

    sys.stdout.write("\nChunking sections based on size: %d \n" % section_sz)

    chunk_dir = "chunk_sections"
    if not os.path.exists(chunk_dir):
        os.makedirs(chunk_dir)

    thread   = ""
    va       = ""
    mnem     = ""
    regs     = ""

    clus_lst_idx = 0
    num_ins   = 0
    seq = 0
    db_idx = -1
    new_sec   = False

    tree = etree.iterparse('vd.xml', events=('end',))

    for cluster in new_cluster_lst:
        if cluster.find('#') != -1:

            # grab the number of ins in cluster
            num = cluster.find('#')
            c_ins_num = int(cluster[num+1:])

            # too small of a cluster to start a section
            if c_ins_num < section_sz and new_sec == False:
                db_idx += c_ins_num
                #print "skipping section - too small ", cluster, c_ins_num, db_idx

            # Bingo! we found our beginning of a new section
            elif c_ins_num >= section_sz and new_sec == False:
                new_sec = True
                db_idx += c_ins_num
                num_ins = 0
                #print "  * Start new section: ", cluster, c_ins_num, db_idx

            # recording how many ins for our new section
            elif c_ins_num < section_sz and new_sec == True:
                num_ins += c_ins_num
                #print "append to new section ", num_ins, db_idx

            # since we are already collecting for our new section, if we
            # find a cluster that exceeds our section size then we have
            # marked the boundaries...go ahead and save off our section
            elif c_ins_num >= section_sz and new_sec == True:

                sec_name =  clus_lst_idx
                #print sec_name, " Record our section ", db_idx, num_ins

                # update our section output table
                val = (db_idx, num_ins)
                section[sec_name].append(val)

                # to account for clusters that were skipped to print out in
                # a new section
                db_idx += num_ins
                #print "after record new section ", db_idx

                # we need to start a new section again as we close a section
                # since it hits our boundary
                # e.g.  -s 9
                # clus__#10
                # clus_#2    <----- start new section 'a'
                # clus__#10  <----- end section 'a'
                # clus_#2    <----- start new section 'b'
                # so reset our number of instructions to record
                num_ins = 0
                #print "  * Start new section 2: ", cluster, c_ins_num, db_idx

                # adjust for that cluster
                db_idx += c_ins_num
                #print "adjust for that cluster: ", db_idx, c_ins_num

            else:
                utils.vd_error("We really should not be here")


        # non-cluster - VA - print out single instruction in the section
        else:
            if new_sec:
                num_ins += 1

            # if we are creating a new section, don't update our starting
            # database pointer (db_idx)
            if new_sec == False:
                db_idx += 1

        clus_lst_idx += 1


    # print out instructions from database
    db_idx = 0
    num_printed = 0
    section = OrderedDict(sorted(section.iteritems()))

    ofile_path_final = os.path.join(chunk_dir, "final_assembly_nasm.asm")
    o_final = open(ofile_path_final, "w")

    for sec_name,v in section.iteritems():
        lst = v[0]
        start_idx = lst[0]
        num_ins   = lst[1]

        #print "start_idx, num_ins: ", start_idx, num_ins

        ofile_path     = os.path.join(chunk_dir, '%s.asm' % sec_name)
        ofile_path_asm = os.path.join(chunk_dir, '%s_nasm.asm' % sec_name)
        o_trace = open(ofile_path, "w")
        o_asm   = open(ofile_path_asm, "w")

        label = "LABEL_" + str(sec_name) + \
        "__________________________________________________________________:\n"
        o_final.writelines(label);

        for action, elem in tree:
            if elem.text is not None:
                if elem.tag == 'thread':
                    thread = elem.text
                elif elem.tag == 'va':
                    va = elem.text
                elif elem.tag == 'mnem':
                    mnem = elem.text + " "
                elif elem.tag == 'regs':
                    regs = elem.text
                    out_t = format_ins_trace(va, mnem, thread, regs, dbgr)
                    out_a = format_ins_asm(mnem, thread, regs, dbgr)
                elif elem.tag == 'ins':

                    # start writing out our instructions for this section
                    if db_idx > start_idx:
                        num_printed += 1
                        if out_t:
                            o_trace.writelines(out_t)
                        else:
                            utils.vd_error("Section file is not open")
                        # certain cases to skip printing...e.g. a JMP
                        # is skipped by format_ins_asm and returns ""
                        if out_a:
                            o_asm.writelines(out_a)
                            o_final.writelines(out_a)

                    # done writing.
                    if num_ins == num_printed:
                        num_printed = 0
                        o_trace.close()
                        o_asm.close()
                        db_idx += 1
                        break

                    db_idx += 1

                utils.progress_bar(5000)

                # eliminate empty refs from root node
                elem.clear()
                while elem.getprevious() is not None:
                    del elem.getparent()[0]

    o_final.close()

