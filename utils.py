#------------------------------------------------------------------------------
# Virtual Deobfuscator Utility Functions
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
# Notes:
#------------------------------------------------------------------------------

import sys

#------------------------------------------------------------------------------
# Configurables
#------------------------------------------------------------------------------
OLLY     = 1
IMMUNITY = 2
WINDBG   = 3

# Output table formats (i.e. window_sz, line_tbl, cluster_tbl)
DEFAULT_DICT = 1
LIST         = 2


BT_ALL_FILE     = "all_backtrace.txt"
VALIDATE_FILE   = "validate.txt"
FORMATTED_FILE  = "rt_formatted.txt"

gen_ids = lambda(x): "".join(map(chr, (ord('a')+(y%26) for y in range(x))))
id_round = gen_ids(26) + '0123456789'

divider = "------------------------------------------------------------------" \
          "--------------\n"

ST_REG = {"ST(0)": "ST0", "ST(1)": "ST1", "ST(2)": "ST2", \
          "ST(3)": "ST3", "ST(4)": "ST4", "ST(5)": "ST5", \
          "ST(6)": "ST6", "ST(7)": "ST7",                 \
          "ST,"  : "ST0,", ",ST ": ",ST0"}


#------------------------------------------------------------------------------
# Error
#------------------------------------------------------------------------------
def vd_error(msg):
    print "\n<!> " + msg
    sys.exit(2)


#------------------------------------------------------------------------------
# Duh!
#------------------------------------------------------------------------------
def is_number_hex(s):
    try:
        int(s, 16)
        return True
    except ValueError:
        return False

#------------------------------------------------------------------------------
#------------------------------------------------------------------------------
def replace_all(text, dic):
    for i, j in dic.iteritems():
        text = text.replace(i, j)
    return text

#------------------------------------------------------------------------------
# Progress bar
#------------------------------------------------------------------------------
def progress_bar(iterations):
    progress_bar.timer += 1

    if progress_bar.timer > iterations:
        sys.stdout.write(".")
        sys.stdout.flush
        progress_bar.timer = 0

progress_bar.timer = 0
