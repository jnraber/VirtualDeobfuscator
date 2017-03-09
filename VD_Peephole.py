#------------------------------------------------------------------------------
# Peephole Optimizer
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
#------------------------------------------------------------------------------

import os
import string
import sys
import re
import random
from idaapi import *

debug = 0  # max is 3

OP_DEST = 0
OP_SRC  = 1

# index values into operand
OP_ID   = 0  # e.g. EAX, 0xDEAD, etc
OP_TYPE = 1  # OPERAND TYPES
OP_SZ   = 2  # OPERAND Size - 8, 4, 2, or 1 bytes
OP_EX   = 3  # OPERAND extended ah to 4 byte EAX

# OPERAND TYPES
OP_GEN_REG      = 1   # General Register
OP_MEM_REF      = 2   # Memory Reference
OP_BASE_IDX     = 3   # Base + Index
OP_BASE_IDX_DIS = 4   # Base + Index + Displacement
OP_IMM          = 5   # Immediate
OP_IMM_FAR      = 6   # Immediate Far Address (with a Segment Selector)
OP_IMM_NEAR     = 7   # Immediate Near Address

ROUND = "1_nasm.asm"

try:
    from collections import defaultdict
except ImportError:
    print("import defaultdict failed")
    idc.Warning("<!> ERROR - import defaultdict failed")

#------------------------------------------------------------------------------
def hdr():
    print "------------------------------------------------------------------"
    print "|                Virutal Deobfuscator's Peephole Optimizer       |"
    print "|                            HexEffect                           |"
    print "------------------------------------------------------------------"
    print ""
    
#------------------------------------------------------------------------------
def vd_hotkey():    
    err = idaapi.CompileLine(r"""
    static key_ALTP()
    {
      RunPythonStatement("VD()");
    }
    """)
    
    if err:
        print "Error compiling IDC code: %s" % err
        return 
    else:
        # Add the hotkey
        AddHotkey("ALT-P", 'key_ALTP')
    
    print "Use ALT+P to use peephole optimizer"
    
#------------------------------------------------------------------------------
# convert hex value to hex string
#------------------------------------------------------------------------------
def hex_str(val, sz=0):
    try:
        # better to see the hex values explicit.
        # -0x1 I would rather see it 0xFF if one byte, etc
        if sz == 1:
            val = hex(val & 0xff)
        elif sz == 2:
            val = hex(val & 0xffff).rstrip("L")
        elif sz == 4:
            # remove trailing L
            val = hex(val & 0xffffffff).rstrip("L")
            
        return val
    except ValueError:
        idc.Warning("<!> ERROR - Not a hex number in hex_str()")
        
#------------------------------------------------------------------------------
# convert string to integer (hex value)
#------------------------------------------------------------------------------
def str_hex(s):
    try:
        s = s.rstrip("L")       
        return int(s, 16)
    except ValueError:
        idc.Warning("<!> ERROR - Not a hex number in str_hex()")

#------------------------------------------------------------------------------
def iterate_instructions():
    mod      = False
    skip_cnt = 0
    cnt      = 0
    idx      = 0
    
    for seg_ea in Segments():
        for ea in Heads(seg_ea, SegEnd(seg_ea)):
            if skip_cnt > cnt:
                mod = True
                cnt += 1
                idx += 1
                continue
            else:
                cnt = 0
                skip_cnt = 0
            
            if isCode(GetFlags(ea)):
                if debug > 0:
                    print "[%08x] %s (%s)" % (ea, GetDisasm(ea), idx)
                ins = Instruction("iterate_instructions", ea, True)
                
                ins.linenum = idx
                idx += 1
                
                peep = PeepHole(ins)
                
                if ins.mnem == 'pop':
                    ins.clear_reg_ins('pop', ins.op1[OP_ID], ins.op1[OP_SZ])
                    
                skip_cnt = peep.push_pop_ind()
                if skip_cnt > 0:
                    continue
                skip_cnt = peep.push_pop_reg()
                if skip_cnt > 0:
                    continue
                skip_cnt = peep.add_add_imm()
                if skip_cnt > 0:
                    continue
                skip_cnt = peep.math_inverse_imm()
                if skip_cnt > 0:
                    continue
                skip_cnt = peep.add_sub_same()
                if skip_cnt > 0:
                    continue

                mod |= peep.mov()
                mod |= peep.math()
                mod |= peep.logical()

                skip_cnt = peep.push()
                if skip_cnt > 0:
                    continue
                skip_cnt = peep.useless_stack() 
                if skip_cnt > 0:
                    continue
                skip_cnt = peep.useless_stack2() 
                if skip_cnt > 0:
                    continue
                skip_cnt = peep.useless_stack3() 
                if skip_cnt > 0:
                    continue
                skip_cnt = peep.push_pop()
                if skip_cnt > 0:
                    continue
                    
                ins.clear_ins()
                
    
    print "Tracked REGS: ", peep.track_regs
    print "Tracked INS: ", peep.track_ins
    #print "PEEPHOLED: ", self.peepholed
    print "Peephole done!"
   
    peep.dump(mod)

#------------------------------------------------------------------------------
def VD():
    try:
        iterate_instructions()
    except:
        print "................................................................"
        traceback.print_exc()
        print "................................................................"
        #idc.Warning("\n\n<!> ERROR\n\n")

#------------------------------------------------------------------------------
class Instruction:
    def __init__(self, func_name, ea, check_dep=False):

        if isCode(GetFlags(ea)) == False:
            self.valid_ins = False
            return
        else:
            self.valid_ins = True
        
        self.linenum = 0
        self.ea = ea
        self.instr = GetDisasm(ea)
        self.mnem = GetMnem(ea)
        self.size = ItemSize(ea)
        
        self.op1 = []
        self.op2 = []
        
        # OP1     
        op_str =  GetOpnd(ea, OP_DEST)
        self.op1.append(op_str)
        type = GetOpType(ea, OP_DEST)
        if type != -1:
            self.op1.append(type)
            
        if type == OP_BASE_IDX or type == OP_BASE_IDX_DIS:
            self.op1.append(4)
        else:
            self.op1.append(self.get_reg_sz(self.op1[OP_ID]))
            
        self.op1.append(self.get_full_reg(self.op1))
            
        # OP2
        op_str =  GetOpnd(ea, OP_SRC)
        self.op2.append(op_str)
        type = GetOpType(ea, OP_SRC)
        if type != -1:
            self.op2.append(type)
            self.op2.append(self.get_reg_sz(self.op2[OP_ID]))
            
            if type == OP_IMM:
                # replace string value with hex value
                value = hex(GetOperandValue(ea, OP_SRC))
                self.op2[OP_ID] = value
        
        if type == OP_BASE_IDX or type == OP_BASE_IDX_DIS:
            self.op1.append(4)
        else:
            self.op2.append(self.get_full_reg(self.op2))
            
        self.check_reg_dependence(func_name)
    
    #--------------------------------------------------------------------------
    def clear_reg_ins(self, mnem, reg, sz, regs_only=True, ins_only=True):

        all_reg = self.get_all_reg_sz(reg, sz)
        # clear registers
        if regs_only:
            for reg_idx in all_reg:                    
                val = PeepHole.track_regs.get(reg_idx)
                if val is not None:
                    if debug > 1:
                        print ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> " \
                              + mnem + " clear [REG] track [", reg_idx, "]", val
                    del PeepHole.track_regs[reg_idx]
        # clear instructions
        if ins_only:
            for reg_idx in all_reg:                    
                val = PeepHole.track_ins.get(reg_idx)
                if val is not None:
                    if debug > 1:
                        print ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> " \
                              + mnem + " clear [INS] track [", reg_idx, "]", val
                    del PeepHole.track_ins[reg_idx]
      
    #--------------------------------------------------------------------------
    def get_all_reg_sz(self, reg, sz):
        all_reg = []
        
        if reg in ['eax', 'ebx', 'ecx', 'edx', 'esi', 'edi', 'esp', 'ebp', \
                   'ax', 'bx', 'cx', 'dx',                                 \
                   'ah', 'al', 'bh', 'bl', 'ch', 'cl', 'dh', 'dl',         \
                   'si', 'di', '[esp]']:
            if sz == 4:  
                if reg[2] == 'x':    # eax
                    lo = reg[1] + 'l'
                    hi = reg[1] + 'h'
                    md = reg[1] + 'x'
                    all_reg.append(reg)
                    all_reg.append(md)
                    all_reg.append(lo)
                    all_reg.append(hi)
                elif reg[2] == 'i':   # edi, esi
                    md = reg[1] + 'i'
                    all_reg.append(reg)
                    all_reg.append(md)
                elif reg[2] == 'p' or reg == '[esp]':
                    all_reg.append(reg)
                else:
                    idc.Warning("\n\n<!> ERROR - get_all_reg_sz()\n\n")
            elif sz == 2: # ax
                if reg[1] == 'x':
                    lo = reg[0] + 'l'
                    hi = reg[0] + 'h'
                    full = 'e' + reg[0] + 'x'
                    all_reg.append(reg)
                    all_reg.append(lo)
                    all_reg.append(hi)
                    all_reg.append(full)
                elif reg[1] == 'i':
                    full = 'e' + reg[0] + 'i'
                    all_reg.append(reg)
                    all_reg.append(full)
                else:
                    idc.Warning("\n\n<!> ERROR - get_all_reg_sz()\n\n")
            elif sz == 1 and (reg[1] == 'h' or reg[1] == 'l'): # ah or al
                all_reg.append(reg)
            else:
                idc.Warning("\n\n<!> ERROR - get_all_reg_sz()\n\n")
            
        return all_reg
            
    #--------------------------------------------------------------------------
    # reset track_ins if register is used as a src operand, this will
    # prevent mov() from optimizing out redundant movs
    #--------------------------------------------------------------------------
    def check_reg_dependence(self, fn):
        src  = self.op2[OP_ID]
        type = self.op2[OP_TYPE]
        
        if type == OP_GEN_REG:
            all_reg = self.get_all_reg_sz(src, self.op2[OP_SZ])
    
            # remove INS tracking
            for reg_idx in all_reg:
                val  = PeepHole.track_ins.get(reg_idx)
                if val is not None:
                    if debug > 1:
                        print ".............................................." \
                              ,fn, "clear ins tracking [", src, "]", self.instr
                    del PeepHole.track_ins[reg_idx]
        elif src and (type == OP_BASE_IDX or type == OP_BASE_IDX_DIS):
            if debug > 1:
                print "..............................................", fn, \
                      "- clear ins tracking [", src, "]", self.instr
            self.clean_ind_reg(src, False, True)
        
    #--------------------------------------------------------------------------
    #--------------------------------------------------------------------------
    def clear_ins(self):
        dest = self.op1[OP_ID]
        src  = self.op2[OP_ID]
        if self.mnem == 'push' or self.mnem == 'pop':
            if self.op1[OP_TYPE] == OP_GEN_REG:
                self.clear_reg_ins(self.mnem, dest, self.op1[OP_SZ])
            elif dest and (self.op1[OP_TYPE] == OP_BASE_IDX       or \
                           self.op1[OP_TYPE] == OP_BASE_IDX_DIS):
                self.clean_ind_reg(dest, True, True)
            self.wipe_esp()
        elif self.mnem == 'lods':
            self.clear_reg_ins(self.mnem, 'esi', 4)
            self.clear_reg_ins(self.mnem, 'eax', 4)
        elif dest.find("esp+") != -1 or src.find("esp+") != -1:
            self.wipe_esp()
        elif dest.find("esp-") != -1 or src.find("esp-") != -1:
            self.wipe_esp()
    
    #--------------------------------------------------------------------------
    def clean_ind_reg(self, op, reg_only, ins_only):
        op_lst = re.split('\+|\*|\[|\]', op)# partition [eax+ebx*4]
        op_lst = filter(None, op_lst)  # remove empyt elements
        for reg in op_lst:
            if reg[0] == 'e':
                self.clear_reg_ins(self.mnem, reg, 4, reg_only, ins_only)
    #--------------------------------------------------------------------------
    def wipe_esp(self):
        self.clear_reg_ins(self.mnem, 'esp', 4)
        self.clear_reg_ins(self.mnem, '[esp]', 4)
        
    #--------------------------------------------------------------------------
    # Size - 8, 4, 2, or 1 bytes
    def get_reg_sz(self, reg):
        reg = reg.lower()
        
        if len(reg) == 3:
            if reg[0] == 'r':
                return 8
            elif reg[0] == 'e':
                return 4
            else:
                return -1
        elif len(reg) == 2:
            if reg[1] == 'x' or reg[1] == 'i':
                return 2
            elif reg[1] == 'h':
                return 1
            elif reg[1] == 'l':
                return 1
            else:
                return 0
        else:
            return 0 

    #--------------------------------------------------------------------------
    def get_full_reg(self, op):
        extended_reg = ""
        
        if op[OP_TYPE] == OP_GEN_REG:
            src = op[OP_ID]
            
            if op[OP_SZ] == 1:
                extended_reg = "e" + src[0] + "x"
            elif op[OP_SZ] == 2:
                if src[1] == 'i':  # di, si
                    extended_reg = "e" + src[0] + "i"
                else:
                    extended_reg = "e" + src[0] + "x"
            else:
                extended_reg = src
                
        return extended_reg 
                
#------------------------------------------------------------------------------
# Data Structures
#              reg      value
# track_regs  {'edx': '0x43691d17', 'eax': '1'}
#
#              reg   linenum(s)  
# track_ins  {'edx': [0, 1],   
#             'eax': [4]
#             'ebx': [5, 6, 7]} 
#
#                       ins            peepholed?
# peepholed   [('add   eax, 0AD34FE1h', False),    ('add  eax, edx', True)
#
class PeepHole:
    
    #---------------------------------------------------------------------------   
    def __init__(self, ins):
        self.ins = ins
        
        # NASM does not like keyword 'ptr'
        ins = self.ins.instr.replace('ptr', '')
        ins = ins.replace('small', '')
        
        # add instruction to peepholed list
        item = (ins, False)
        PeepHole.peepholed.append(item)
        
        
    #---------------------------------------------------------------------------   
    def logical(self):
        mod = False
        
        dest     = self.ins.op1[OP_ID]
        src      = self.ins.op2[OP_ID]
        dest_sz  = self.ins.op1[OP_SZ]
        src_sz   = self.ins.op2[OP_SZ]
        dest_val = PeepHole.track_regs.get(dest)
        src_val  = PeepHole.track_regs.get(src)
        mnem     = self.ins.mnem 

        #----------------------------------------------------------------------
        # SHR/SHL
        #----------------------------------------------------------------------
        if (mnem == 'shr' or mnem == 'shl') and dest_val is not None:
            if self.ins.op1[OP_TYPE] == OP_GEN_REG:
                if self.ins.op2[OP_TYPE] == OP_IMM:
                    
                    if mnem == 'shr':
                        res = str_hex(dest_val) >> str_hex(src)
                        res = hex_str(res, dest_sz)
                        if debug > 0:
                            print "SHR ", res
                    else:
                        res = str_hex(dest_val) << str_hex(src)
                        res = hex_str(res, dest_sz)
                        if debug > 0:
                            print "SHL ", res
                    
                    mod = PeepHole.gen_mov(self, res, dest, self.ins, mnem)
                    
        return mod

    #---------------------------------------------------------------------------   
    def math(self):
        mod = False
        
        dest      = self.ins.op1[OP_ID]
        src       = self.ins.op2[OP_ID]
        dest_type = self.ins.op1[OP_TYPE]
        src_type  = self.ins.op2[OP_TYPE]
        dest_sz   = self.ins.op1[OP_SZ]
        src_sz    = self.ins.op2[OP_SZ]
        dest_val  = PeepHole.track_regs.get(dest)
        src_val   = PeepHole.track_regs.get(src)
        mnem      = self.ins.mnem 
        
        #----------------------------------------------------------------------
        # DEC/INC
        #----------------------------------------------------------------------
        if (mnem == 'dec' or mnem == 'inc') and dest_val is not None:
            if dest_type == OP_GEN_REG:
                if mnem == 'dec':
                    res = str_hex(dest_val) - 1
                else:
                    res = str_hex(dest_val) + 1
                res = hex_str(res, dest_sz)
                if debug > 0:
                    print mnem.upper(), res
                mod = PeepHole.gen_mov(self, res, dest, self.ins, mnem)
        #----------------------------------------------------------------------
        # NOT
        #----------------------------------------------------------------------
        elif mnem == 'not' and dest_val is not None: 
            if dest_type == OP_GEN_REG:
                res = ~str_hex(dest_val)
                res = hex_str(res, dest_sz)
                if debug > 0:
                    print mnem.upper(), res
                PeepHole.track_regs[dest] = res 
                mod = PeepHole.gen_mov(self, res, dest, self.ins, mnem)
        #----------------------------------------------------------------------
        # NEG
        #----------------------------------------------------------------------
        elif mnem == 'neg' and dest_val is not None: 
            if dest_type == OP_GEN_REG:
                dest_val = "-" + dest_val
                res = str_hex(dest_val)
                res = hex_str(res, dest_sz)
                if debug > 0:
                    print mnem.upper(), res
                PeepHole.track_regs[dest] = res
                mod = PeepHole.gen_mov(self, res, dest, self.ins, mnem)
        #----------------------------------------------------------------------
        # Peephole 1:
        # ADD/SUB
        # ADD REG, VAL  ; becomes  MOV REG, VAL
        #
        # Peephole 2:
        # ADD REG1, REG2  ; becomes ADD REG1, VAL ; if we know REG2's value
        #----------------------------------------------------------------------
        elif (mnem == 'add' or mnem == 'sub'):
            if dest_val is not None:
                # Peephole 1 
                if dest_type == OP_GEN_REG and src_type == OP_IMM:
                    if mnem == 'add':
                        res = str_hex(dest_val) + str_hex(self.ins.op2[OP_ID])
                    else:
                        res = str_hex(dest_val) - str_hex(self.ins.op2[OP_ID])
                    
                    res = hex_str(res, dest_sz)
                    mod = PeepHole.gen_mov(self, res, dest, self.ins, mnem)
    
                # Peephole 2
                else:
                    mod = PeepHole.swap_src_w_imm(self, dest_type, src_type,
                                                  src, dest, self.ins, mnem,
                                                  src_val)
            elif src_val is not None:
                mod = PeepHole.swap_src_w_imm(self, dest_type, src_type, src,
                                              dest, self.ins, mnem, src_val)
        
        #----------------------------------------------------------------------
        # XOR/OR
        # Peephole 1:
        # XOR/OR REG, VAL   ; becomes MOV REG, RESULT
        #
        # Peephole 2:
        # XOR/OR REG1, REG2   ; becomes XOR/OR REG, VAL if we know REG2's value
        #----------------------------------------------------------------------
        elif (mnem == 'xor' or mnem == 'or'):
            if dest_val is not None:
                # Peephole 1
                if dest_type == OP_GEN_REG and src_type == OP_IMM:
                    if mnem == 'xor':
                        src = hex(str_hex(dest_val) ^ str_hex(self.ins.op2[OP_ID]))
                    else:
                        src = hex(str_hex(dest_val) | str_hex(self.ins.op2[OP_ID]))
            
                    src = hex_str(src, src_sz)
                    mod = PeepHole.gen_mov(self, src, dest, self.ins, mnem)
                # Peephole 2
                else:
                    mod = PeepHole.swap_src_w_imm(self, dest_type, src_type,
                                                  src, dest, self.ins, mnem,
                                                  src_val)
            elif src_val is not None:
                mod = PeepHole.swap_src_w_imm(self, dest_type, src_type, src,
                                              dest, self.ins, mnem, src_val)
                        
        #----------------------------------------------------------------------
        # AND
        #----------------------------------------------------------------------
        elif mnem == 'and' and dest_val is not None:
            if src_type == OP_IMM:
                src = hex(str_hex(dest_val) & str_hex(self.ins.op2[OP_ID]))
                mod = PeepHole.gen_mov(self, src, dest, self.ins, mnem)
                
        return mod
    


    #---------------------------------------------------------------------------
    # PEEPHOLE 1:
    # MOV REG1, REG2  -> if we know REG2 then replace it with the imm val
    # 
    # Remove ins that are useless (as long as not dependence on prev mov)
    # PEEPHOLE 2:
    # mov edx, 1  <----- removed
    # dec edx     <----- removed
    # ...
    # mov edx, 3
    #---------------------------------------------------------------------------
    def mov(self):
        mod = False
        dest = self.ins.op1[OP_ID]
        src  = self.ins.op2[OP_ID]
        dest_type = self.ins.op1[OP_TYPE]
        dest_sz   = self.ins.op1[OP_SZ]
        src_type  = self.ins.op2[OP_TYPE]
        mnem      = self.ins.mnem 

        if mnem == 'mov':
            src_val = PeepHole.track_regs.get(src)
            
            #------------------------------------------------------------------
            # PEEPHOLE 1
            #------------------------------------------------------------------
            if src_val is not None and src_type == OP_GEN_REG:
                mod = PeepHole.replace_src_w_imm(self, src, dest,
                                                 self.ins, mnem, src_val)
                
                mod = PeepHole.purge_prev_ins(self, dest, 'mov')
                
                PeepHole.track_regs[dest] = src_val
                PeepHole.track_ins[dest].append(self.ins.linenum)
            #------------------------------------------------------------------
            # PEEPHOLE 2
            #------------------------------------------------------------------
            else:
                # start tracking ins MOVs regsiter and value
                if dest_type == OP_GEN_REG and src_type == OP_IMM:
                    src = str_hex(src)
                    PeepHole.track_regs[dest] = hex_str(src, dest_sz)
                
                mod = PeepHole.purge_prev_ins(self, dest, 'mov')
                PeepHole.track_ins[dest].append(self.ins.linenum)
        # any other instruction add to list, except a push (stack integrity)
        else:
            if dest_type == OP_GEN_REG:
                if mnem != 'push':
                    PeepHole.track_ins[dest].append(self.ins.linenum)
        return mod
    
    #---------------------------------------------------------------------------
    # PUSH REG   <---- remove
    # ...      as long as no use of REG  or another push/stack manipulation
    #          only go through 5 total ins
    # POP REG    <----- remove
    #   or
    # MOV REG, val   <---- remove
    # POP REG
    #---------------------------------------------------------------------------
    def push_pop(self):
        ins_skip  = 0
        mnem = self.ins.mnem
        
        #-----------------------------------------------------------------------
        # PUSH REG or MOV REG, val
        # ...
        # POP REG
        #-----------------------------------------------------------------------
        if (mnem == 'push' and self.ins.op1[OP_TYPE] == OP_GEN_REG) or \
           (mnem == 'mov'  and self.ins.op1[OP_TYPE] == OP_GEN_REG     \
            and self.ins.op2[OP_TYPE] == OP_IMM):
           
            ins_depth = 5
            optimized = []
            ex_src    = ""
            ex_dest   = ""

            # just in case we run into a MOV DH, VAL we want the extended
            # version of DH -> EDX, so if we encounter a POP EDX we can
            # remove the MOV
            tracked_reg = self.ins.op1[OP_EX]
            
            ins = PeepHole.nxt_ins(self, "push_pop", self.ins)
            if ins.valid_ins == False: return 0
            
            for i in range(ins_depth):
                # make sure esp is not being used as either operand
                # e.g. add [esp+4], value or another push happens
                #if ins.instr.find("esp") != -1 or \
                #   (self.ins.mnem == 'push' and ins.mnem == 'push'):
                if ins.instr.find("esp") != -1 or ins.mnem == 'push':
                    if debug > 2:
                        print "* push_pop() - Stack integrity is compromised",\
                               ins.instr, "\n"
                    return 0
                
                # look for derivatives of register, to make sure it is not
                # being used as a src operand
                if ins.op2[OP_TYPE] == OP_GEN_REG:
                    ex_src = ins.op2[OP_EX]
                    if ex_src == tracked_reg:
                        if debug > 2:
                            print "* push_pop() - dep lo/hi ins:", ins.instr
                        return 0

                # here we want to capture ins that use the tracked reg
                # as a destination, if so we will mark for deletion below
                ex_dest = ins.op1[OP_EX]
                        
                # Check if our tracked reg is ever used as a dest, if
                # so mark it for deletion
                if ins.op1[OP_TYPE] == OP_GEN_REG and \
                   (ins.op1[OP_ID] == tracked_reg or ex_dest == tracked_reg):
                        cmt = ";(%s_pop) %s" % (self.ins.mnem, ins.instr)
                        optimized.append(cmt)
                # Otherwise just tack it on
                else:
                    # to be safe, delete any tracking for registers used in
                    # between push/pop
                    if ins.op1[OP_TYPE] == OP_GEN_REG:
                        ins.clear_reg_ins(ins.mnem, ins.op1[OP_ID],
                                          ins.op1[OP_SZ])
                    optimized.append(ins.instr)
                    
                # Check for a POP
                if ins.mnem == 'pop' and ex_dest == tracked_reg:
                   if debug > 0:
                        print "\n-->(%s_pop): %s\n" % \
                               (self.ins.mnem, self.ins.instr)
                   ins_skip = i + 1  # i starts at 0 - account for the first pop
                   
                   # skip last optimization (POP REG), if we start tracking
                   # with a mov...ins
                   if mnem == 'mov':
                      optimized.pop()
                      optimized.append(ins.instr)

                   break
                
                ins = PeepHole.nxt_ins(self, "push_pop", ins)
                if ins.valid_ins == False: return 0
        
            # replace the PUSH/MOV ins, then tack on the rest
            if ins_skip > 0:
                idx = len(PeepHole.peepholed)
                commented = ";(%s_pop) %s" % (self.ins.mnem, self.ins.instr)
                item = (commented, True)
                PeepHole.peepholed[idx-1] = item
        
                for new_ins in optimized:
                    item = (new_ins, True)
                    PeepHole.peepholed.append(item)
                    
                if self.ins.mnem == 'mov':
                    ins.clear_reg_ins('mov', self.ins.op1[OP_ID],
                                      self.ins.op1[OP_SZ])
                
        return ins_skip
    
    #---------------------------------------------------------------------------
    # PUSH REG1  or dword [esp] 
    # POP REG2   ; replace the "MOV REG2, REG1"
    #---------------------------------------------------------------------------
    def push_pop_reg(self):
        ins_skip  = 0
        mnem = self.ins.mnem
        
        if mnem == 'push':
            optimized = []

            src = self.ins.op1[OP_ID]
            
            ins = PeepHole.nxt_ins(self, "push_pop_reg", self.ins)
            if ins.valid_ins == False: return 0
            
            # POP dest
            if (ins.mnem == 'pop') == False:
                return 0
            
            dest = ins.op1[OP_ID]
            new_ins = "mov\t" + dest + ", " + src.ljust(20) +  \
                      ";(push_pop_reg) " + ins.instr
            optimized.append(new_ins)

            PeepHole.update_peep_lst(self, optimized, self.ins.instr,
                                     "push_pop_reg")
            ins_skip = 1

        return ins_skip
    #---------------------------------------------------------------------------
    # PUSH REG   
    # MOV REG, VAL
    # ADD DWORD [ESP+4], VAL
    # POP REG    ; replace the whole sequence with "ADD [esp], val"
    #---------------------------------------------------------------------------
    def push_pop_ind(self):
        ins_skip  = 0
        mnem = self.ins.mnem
        
        if mnem == 'push' and self.ins.op1[OP_TYPE] == OP_GEN_REG:
            optimized = []

            tracked_reg = self.ins.op1[OP_ID]
            
            ins = PeepHole.nxt_ins(self, "push_pop_ind", self.ins)
            if ins.valid_ins == False: return 0
            
            # MOV REG, VAL
            if (ins.mnem == 'mov' and ins.op1[OP_ID] == tracked_reg and \
               ins.op2[OP_TYPE] == OP_IMM) == False:
                return 0
            
            cmt = ";(push_pop_ind) " + ins.instr
            optimized.append(cmt)
            
            # ADD [esp+4], VAL
            ins = PeepHole.nxt_ins(self, "push_pop_ind", ins)
            if ins.valid_ins == False: return 0
            ind = ins.op1[OP_ID]
            base = ind.find("[esp+4]") 
            if (ins.mnem == 'add' and base != -1 and \
                ins.op2[OP_TYPE] == OP_IMM) == False:
                return 0
            
            immediate = ins.op2[OP_ID]
            cmt = ";(push_pop_ind) " + ins.instr
            optimized.append(cmt)

            # POP REG
            ins = PeepHole.nxt_ins(self, "push_pop_ind", ins)
            if ins.valid_ins == False: return 0

            if (ins.mnem == 'pop' and ins.op1[OP_ID] == tracked_reg) == False:
                return 0

            new_ins = "add dword[esp], " + immediate +  \
                      ";(push_pop_ind) " + ins.instr
            optimized.append(new_ins)

            PeepHole.update_peep_lst(self, optimized, self.ins.instr,
                                     "push_pop_ind")
            ins_skip = 3

        return ins_skip
    
    #---------------------------------------------------------------------------
    # PUSH VALUE  or PUSH REG
    # MOV [esp], REG            ; replace by push reg
    #---------------------------------------------------------------------------
    def push(self):
        ins_skip = 0

        if self.ins.mnem == 'push' and (self.ins.op1[OP_TYPE] == OP_IMM or \
                                        self.ins.op1[OP_TYPE] == OP_GEN_REG):

            ins = PeepHole.nxt_ins(self, "push",self.ins)
            if ins.valid_ins == False: return 0
            
            linenum_push = self.ins.linenum
            
            if ins.mnem == 'mov' and ins.op1[OP_TYPE] == OP_BASE_IDX and  \
               ins.op2[OP_TYPE] == OP_GEN_REG:
               
                first = PeepHole.peepholed[linenum_push]
                if debug > 0:
                    print "\n-->(push): ", first[0], "\n"
               
                PeepHole.replace_last_peepholed(self, "push", "push",
                                                ins.op2[OP_ID])
                
                item = (";(push) " + ins.instr, True)
                PeepHole.peepholed.append(item)
                
                ins_skip = 1
                
        return ins_skip

    #---------------------------------------------------------------------------
    # ADD REG, val
    #   sometimes ins in between
    # ADD REG, val  ; ADD REG, val+val
    # We don't know what is in REG
    #---------------------------------------------------------------------------
    def add_add_imm(self):
        ins_skip  = 0
        possible_extra_skip = 0
        mnem = self.ins.mnem
        optimized = []

        if (mnem == 'add' or mnem == 'sub') == False:
            return 0
            
        if self.ins.op2[OP_TYPE] == OP_IMM:
            reg1 = self.ins.op1[OP_ID]
            val1 = self.ins.op2[OP_ID]

            ins = PeepHole.nxt_ins(self, "add_add_imm", self.ins)
            if ins.valid_ins == False: return 0
            
            if (ins.op2[OP_TYPE] == OP_IMM) == False: 
                # take one more shot...look at next ins and make sure it is not
                # using our tracked register
                if ins.op1[OP_ID] != reg1 and ins.op2[OP_ID] != reg1:
                    # save off that middle ins and take a look at the next
                    optimized.append(ins.instr)
                    ins.clear_ins()

                    ins = PeepHole.nxt_ins(self, "add_add_imm", ins)
                    if ins.valid_ins == False: return 0
                    possible_extra_skip = 1
                    
                    if (ins.op2[OP_TYPE] == OP_IMM) == False:
                        return 0
                else:
                    return 0
            
            reg2  = ins.op1[OP_ID]
            val2  = ins.op2[OP_ID]
            op_sz = ins.op1[OP_SZ]
            
            if reg1 != reg2:
                return 0
           
            # ADD REG, IMM1
            # SUB REG, IMM2 ; so long as IMM1 > IMM2
            if ins.mnem != mnem:
                if mnem == 'add' and str_hex(val1) > str_hex(val2):
                    total = str_hex(val1) - str_hex(val2)
                else:
                    return 0
            else:
                total = str_hex(val1) + str_hex(val2)
            
            final = hex_str(total, op_sz)

            # For this optimization, put final result first, I do this b/c
            # other simple peephole opts will be ineffect
            # i.e.
            #      add  reg, final_result   ; add reg, val1
            #      ; add reg, val2
            cmt = ";(add_add_imm) " + ins.instr
            optimized.append(cmt)
            
            new_ins = mnem + "\t\t" + reg1 + ", " + final.ljust(20) +  \
                      ";(add_add_imm) " + self.ins.instr
            if debug > 0:
                print "\n-->", new_ins

            item = (new_ins, True)
            idx = len(PeepHole.peepholed)
            PeepHole.peepholed[idx-1] = item

            for new_ins in optimized:
                new_ins = new_ins.replace('ptr', '')
                item = (new_ins, True)
                PeepHole.peepholed.append(item)
            
            ins_skip = 1 + possible_extra_skip 
        return ins_skip
    
    #---------------------------------------------------------------------------
    # 1: add eax, 1  <--- remove   or sub eax, 1
    # 2: don't care
    # 3: sub eax, 1  <--- remove      add eax, 1
    #---------------------------------------------------------------------------
    def math_inverse_imm(self):
        ins_skip  = 0
        mnem = self.ins.mnem

        if (mnem == 'add' or mnem == 'sub') == False:
            return 0
            
        optimized = []

        if self.ins.op2[OP_TYPE] == OP_IMM:
            dest1 = self.ins.op1[OP_ID]
            val1  = self.ins.op2[OP_ID]
    
            # go to next ins, then skip it
            ins = PeepHole.nxt_ins(self, "math_inverse_imm", self.ins)
            if ins.valid_ins == False: return 0
            optimized.append(ins.instr)
            ins.clear_ins()

            # 3rd ins
            ins = PeepHole.nxt_ins(self, "math_inverse_imm", ins)
            if ins.valid_ins == False: return 0
            if (ins.op2[OP_TYPE] == OP_IMM) == False:
                return 0
            
            # make sure 3rd ins is the inverse i.e add->sub, sub->add
            if ((mnem == 'add' and ins.mnem == 'sub') or \
                (mnem == 'sub' and ins.mnem == 'add')) == False:
                return 0
            
            dest2 = ins.op1[OP_ID]
            val2  = ins.op2[OP_ID]
            op_sz = ins.op1[OP_SZ]
            
            if dest1 != dest2 or val1 != val2:
                return 0
           
            cmt = ";(math_inverse_imm) " + ins.instr
            
            if debug > 0:
                print "\n-->", cmt
            optimized.append(cmt)

            PeepHole.update_peep_lst(self, optimized, self.ins.instr,
                                     "math_inverse_imm")
            ins_skip = 2
        return ins_skip

    #---------------------------------------------------------------------------
    # 1: push reg
    # 2: mov reg, esp
    # 3: add reg, 8
    # 4: xchg reg, [esp]
    # 5: pop reg          ; all replaced with "add esp, 4"
    #     OR
    # 5: mov esp, [esp]   ; all replaced with "add esp, 4"
    #---------------------------------------------------------------------------
    def useless_stack(self):
        ins_skip  = 0
        mnem = self.ins.mnem

        if (mnem == 'push' and self.ins.op1[OP_TYPE] == OP_GEN_REG) == False:
            return 0
            
        reg = self.ins.op1[OP_ID]
        optimized = []

        # 2: MOV REG, ESP
        ins = PeepHole.nxt_ins(self, "useless_stack", self.ins)
        if ins.valid_ins == False: return 0
        if (ins.mnem       == 'mov' and ins.op1[OP_TYPE] == OP_GEN_REG and \
            ins.op1[OP_ID] == reg   and ins.op2[OP_TYPE] == OP_GEN_REG and \
            ins.op2[OP_ID] == 'esp') == False:
            return 0

        cmt = ";(useless_stack) " + ins.instr
        optimized.append(cmt)

        # 3: ADD REG, 8
        ins = PeepHole.nxt_ins(self, "useless_stack", ins)
        if ins.valid_ins == False: return 0
        if (ins.mnem       == 'add' and ins.op1[OP_TYPE] == OP_GEN_REG and \
            ins.op1[OP_ID] == reg   and ins.op2[OP_TYPE] == OP_IMM     and \
            str_hex(ins.op2[OP_ID]) == 8) == False:
            return 0

        cmt = ";(useless_stack) " + ins.instr
        optimized.append(cmt)

        # 4: XCHG reg, [esp]   or   XCHG [esp], reg
        ins = PeepHole.nxt_ins(self, "useless_stack", ins)
        if ins.valid_ins == False: return 0
        if ins.mnem == 'xchg' and \
           (ins.op1[OP_TYPE] == OP_GEN_REG  and ins.op1[OP_ID] == reg      and \
            ins.op2[OP_TYPE] == OP_BASE_IDX and ins.op2[OP_ID] == '[esp]') or  \
           (ins.op1[OP_TYPE] == OP_BASE_IDX and ins.op1[OP_ID] == '[esp]'  and \
            ins.op2[OP_TYPE] == OP_GEN_REG  and ins.op2[OP_ID] == reg): 
            
            cmt = ";(useless_stack) " + ins.instr
            optimized.append(cmt)
    
            # 5: pop esp    or    mov esp, [esp]
            ins = PeepHole.nxt_ins(self, "useless_stack", ins)
            if ins.valid_ins == False: return 0
            
            if (ins.mnem       == 'pop' and ins.op1[OP_TYPE] == OP_GEN_REG and \
                ins.op1[OP_ID] == 'esp') \
                 or                      \
                (ins.mnem      == 'mov' and ins.op1[OP_TYPE] == OP_GEN_REG and \
                 ins.op1[OP_ID] == 'esp' and ins.op2[OP_ID] == '[esp]'):
    
                new_ins = "add\t\tesp, 4"
                cmt = new_ins.ljust(20) + ";(useless_stack) " + ins.instr
                
                if debug > 0:
                    print "\n-->(useless_stack)", ins.instr, "\n"
                optimized.append(cmt)
        
                PeepHole.update_peep_lst(self, optimized, self.ins.instr,
                                         "useless_stack")
                ins_skip = 4
        return ins_skip

    #---------------------------------------------------------------------------
    # 1: push reg
    # 2: mov reg, esp
    # 3: xchg reg, [esp]
    # 4: pop esp
    # 5: mov [esp], reg2    ; all of these ins...replaced with "push reg2"
    #---------------------------------------------------------------------------
    def useless_stack2(self):
        ins_skip  = 0
        mnem = self.ins.mnem

        if (mnem == 'push' and self.ins.op1[OP_TYPE] == OP_GEN_REG) == False:
            return 0
            
        reg = self.ins.op1[OP_ID]
        optimized = []

        # 2: MOV REG, ESP
        ins = PeepHole.nxt_ins(self, "useless_stack2", self.ins)
        if ins.valid_ins == False: return 0
        if (ins.mnem       == 'mov' and ins.op1[OP_TYPE] == OP_GEN_REG and \
            ins.op1[OP_ID] == reg   and ins.op2[OP_TYPE] == OP_GEN_REG and \
            ins.op2[OP_ID] == 'esp') == False:
            return 0

        cmt = ";(useless_stack 2) " + ins.instr
        optimized.append(cmt)

        # 3: XCHG reg, [esp]   or   XCHG [esp], reg
        ins = PeepHole.nxt_ins(self, "useless_stack2", ins)
        if ins.valid_ins == False: return 0
        if ins.mnem == 'xchg' and \
           (ins.op1[OP_TYPE] == OP_GEN_REG  and ins.op1[OP_ID] == reg      and \
            ins.op2[OP_TYPE] == OP_BASE_IDX and ins.op2[OP_ID] == '[esp]') or  \
           (ins.op1[OP_TYPE] == OP_BASE_IDX and ins.op1[OP_ID] == '[esp]'  and \
            ins.op2[OP_TYPE] == OP_GEN_REG  and ins.op2[OP_ID] == reg): 
            
            cmt = ";(useless_stack 2) " + ins.instr
            optimized.append(cmt)
    
            # 4: pop esp
            ins = PeepHole.nxt_ins(self,"useless_stack2", ins)
            if ins.valid_ins == False: return 0
            if (ins.mnem       == 'pop' and ins.op1[OP_TYPE] == OP_GEN_REG and \
                ins.op1[OP_ID] == 'esp') == False:
                return 0

            cmt = ";(useless_stack 2) " + ins.instr
            optimized.append(cmt)
    
            # 5: mov [esp], reg2
            ins = PeepHole.nxt_ins(self, "useless_stack2", ins)
            if ins.valid_ins == False: return 0
            if (ins.mnem == 'mov' and ins.op1[OP_TYPE] == OP_BASE_IDX and \
                ins.op1[OP_ID] == '[esp]' and ins.op2[OP_TYPE] == OP_GEN_REG \
                and ins.op2[OP_ID] != reg ) == False:
                return 0
            
            new_ins = "push\t\t" + ins.op2[OP_ID]
            cmt = new_ins.ljust(20) + ";(useless_stack 2) " + ins.instr
            
            if debug > 0:
                print "\n-->(useless_stack 2)", ins.instr, "\n"
            optimized.append(cmt)
    
            PeepHole.update_peep_lst(self, optimized, self.ins.instr,
                                     "useless_stack 2")
            ins_skip = 4
        return ins_skip
    
    #---------------------------------------------------------------------------
    # 1: push cx
    # 2: mov cx, [esp]     ; remove this ins
    # 3: add esp, 2
    #---------------------------------------------------------------------------
    def useless_stack3(self):
        ins_skip  = 0
        mnem = self.ins.mnem

        if (mnem == 'push' and self.ins.op1[OP_TYPE] == OP_GEN_REG) == False:
            return 0
            
        reg = self.ins.op1[OP_ID]
        optimized = []

        # 2: MOV REG(16-bit), [ESP]
        ins = PeepHole.nxt_ins(self, "useless_stack3", self.ins)
        if ins.valid_ins == False: return 0
        if (ins.mnem       == 'mov' and ins.op1[OP_TYPE] == OP_GEN_REG  and \
            ins.op1[OP_ID] == reg   and ins.op2[OP_TYPE] == OP_BASE_IDX and \
            ins.op2[OP_ID] == '[esp]') == False:
            return 0

        cmt = ";(useless_stack3) " + ins.instr
        optimized.append(cmt)

        # 3: ADD esp, 2
        ins = PeepHole.nxt_ins(self, "useless_stack3", ins)
        if ins.valid_ins == False: return 0
        if (ins.mnem       == 'add' and ins.op1[OP_TYPE] == OP_GEN_REG and \
            ins.op2[OP_TYPE] == OP_IMM                                 and \
            str_hex(ins.op2[OP_ID]) == 2):

                optimized.append(ins.instr)
                if debug > 0:
                    print "\n-->(useless_stack3)", ins.instr, "\n"
        
                PeepHole.update_peep_lst(self, optimized, self.ins.instr,
                                         "useless_stack3", False)
                ins_skip = 2
        return ins_skip
    #---------------------------------------------------------------------------
    def update_peep_lst(self, optimized, instr, type, peep_last=True):
        # add first instruction then append the rest to peepholed list
        # by deleteing the last element to the peepholed list
        if peep_last:
            idx = len(PeepHole.peepholed)
            cmt = ";(" + type + ") " + instr
            item = (cmt, True)
            PeepHole.peepholed[idx-1] = item

        for new_ins in optimized:
            new_ins = new_ins.replace('ptr', '')
            item = (new_ins, True)
            PeepHole.peepholed.append(item)
        
    #---------------------------------------------------------------------------
    # add eax, 1  <--- remove
    # sub eax, 1  <--- remove
    #---------------------------------------------------------------------------
    def add_sub_same(self):
        ins_skip  = 0
        mnem  = self.ins.mnem
        type1 = self.ins.op1[OP_TYPE]
        type2 = self.ins.op2[OP_TYPE]
        
        if (mnem == 'add' and type1 == OP_GEN_REG and type2 == OP_IMM) == False:
            return 0
            
        reg  = self.ins.op1[OP_ID]
        val1 = self.ins.op2[OP_ID]
        
        optimized = []

        # 2: sub eax, val
        ins = PeepHole.nxt_ins(self, "add_sub_same", self.ins)
        if ins.valid_ins == False:
            return 0
        
        if ins.mnem       == 'sub' and ins.op1[OP_TYPE] == OP_GEN_REG and \
           ins.op1[OP_ID] == reg   and ins.op2[OP_TYPE] == OP_IMM:
            
            val2 = ins.op2[OP_ID]
            if str_hex(val1) == str_hex(val2):
                cmt = ";(add_sub_same) " + ins.instr
                optimized.append(cmt)
                
                PeepHole.update_peep_lst(self, optimized, self.ins.instr,
                                         "add_sub_same")
                ins_skip = 1

        return ins_skip

    #---------------------------------------------------------------------------   
    def nxt_ins(self, func_name, ins):    
        return Instruction(func_name, ins.ea + ins.size)
        
    #---------------------------------------------------------------------------   
    def gen_mov(self, res, dest, ins, src_mnem):
        PeepHole.replace_last_peepholed(self, "mov", src_mnem, dest, res)
        
        if debug > 0:
            print "\n-->- %s reg, NEW_VAL[%s]\n" % (src_mnem, res)
            
        PeepHole.track_regs[dest] = res
        
        return True
        
    #---------------------------------------------------------------------------   
    def dump(self, mod):
        ofile_asm = ROUND 
        o_asm = open(ofile_asm, "w")
    
        print "----------------------------------------------------------------"
        if mod:
            print "Deobfuscated results written to: ", ofile_asm
        else:
            print "No more Deobfuscations - check file for final: ", ofile_asm
        print "----------------------------------------------------------------"
        print "" 
        for ins, is_mod in self.peepholed:
            
            # NASM does not like keyword 'ptr'
            ins = ins.replace('ptr', '')
            ins = ins.replace('small', '')
            
            ins_formated = "\t" + ins + "\n"
            o_asm.writelines(ins_formated)
            
        o_asm.close()
            
    #---------------------------------------------------------------------------   
    def replace_last_peepholed(self, mnem, src_mnem, dest, src=None):
        # replace last instruction with a new 'mnem dest, src'
        idx = len(PeepHole.peepholed)
        
        if src is not None:
            new_instr = mnem + "\t\t" + dest + ", " + str(src).ljust(20) + \
                        "; [(%s)] %s" % (src_mnem, self.ins.instr)
        else:
            new_instr = mnem.ljust(8) + dest.ljust(20) + \
                        "; [(%s)] %s" % (src_mnem, self.ins.instr)
            
        item = (new_instr, True)
        PeepHole.peepholed[idx-1] = item
        
    #---------------------------------------------------------------------------   
    def swap_src_w_imm(self, d_type, s_type, src, dest, ins, mnem, src_val):
        mod = False
        
        if d_type == OP_GEN_REG or d_type == OP_BASE_IDX_DIS and \
            s_type == OP_GEN_REG:
            if src_val is not None:
                mod = PeepHole.replace_src_w_imm(self, src, dest,
                                                 ins, mnem, src_val)
            else:
                PeepHole.clear_reg_tracking(self, dest, self.ins.instr)
                
        return mod
    #---------------------------------------------------------------------------   
    def replace_src_w_imm(self, src, dest, ins, mnem, src_val):
        src_mnem = mnem
        if ins.op1[OP_TYPE] == OP_BASE_IDX_DIS:
            mnem = mnem + "\t\tdword "
            
        PeepHole.replace_last_peepholed(self, mnem, src_mnem, dest, src_val)

        if debug > 0:
            print "\n-->- %s reg, NEW_VAL[%s]\n" % (mnem, src_val)

        PeepHole.clear_reg_tracking(self, dest, ins.instr)
        
        return True
        
    #---------------------------------------------------------------------------   
    # reset the optype....so we don't screw up the check_reg_dependence()
    #---------------------------------------------------------------------------   
    def update_op(self, dest, op_type, src_val):
        if dest == OP_SRC:
            self.ins.op2[OP_TYPE] = op_type
            self.ins.op2[OP_ID]   = src_val
        else:
            self.ins.op1[OP_TYPE] = op_type
            self.ins.op1[OP_ID]   = src_val
            
    #---------------------------------------------------------------------------
    # Purge ins that are affected by dest getting overwritten
    # loop over all instr that have dest as tracked reg and del
    #---------------------------------------------------------------------------
    def purge_prev_ins(self, dest, type):
        line_lst = PeepHole.track_ins.get(dest)
        if line_lst is None:
            return False
        
        for linenum in line_lst:
            old = PeepHole.peepholed[linenum]
            str = ";(" + type + ") " + old[0] + " > WHO " + self.ins.instr
            item = (str, True)
            if debug > 0:
                print "\n", str
            PeepHole.peepholed[linenum] = item
        
        del PeepHole.track_ins[dest]
        
        return True
    
    #---------------------------------------------------------------------------   
    def clear_reg_tracking(self, reg, instr):
        val = PeepHole.track_regs.get(reg)
        if val is not None:
            if debug > 1:
                print "....................clear reg tracking reg: %s [%s]" % \
                      (reg, instr)
            del PeepHole.track_regs[reg]
    
PeepHole.track_regs = {}
PeepHole.track_ins = defaultdict(list)
PeepHole.peepholed = []

#------------------------------------------------------------------------------
def my_main():
    
    hdr()
    
    #vd_hotkey()
    VD()
    
#------------------------------------------------------------------------------
my_main()    
