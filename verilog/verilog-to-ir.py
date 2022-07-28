from pyosys import libyosys as ys
import sys

class IR:
    _fields = ()
    def __init__(self, *args):
        for n,x in zip(self._fields, args):
            setattr(self, n, x)

class Decl(IR):
    _fields = ('id', 'port_type', 'args', 'name')
    def __str__(self, varmap=None):
        decl_id = ""
        if isinstance(self.id, Wire):
            decl_id = self.id.__str__(varmap)
        elif varmap:
            decl_id = str(varmap[self.id])
        else:
            decl_id = str(self.id)
        args_pp = ""
        if str(self.port_type) == "HOLE":
            args_pp = str(self.args[0]) + \
                      ' (list {})'.format(' '.join([str(varmap[x]) \
                                              if varmap else str(x) \
                                              for x in self.args[1].split(' ')]))
        else:
            args_pp = ' '.join(str(x) for x in self.args)
        return '({} ({} {} \"{}\"))'.format(decl_id, \
                                            str(self.port_type), \
                                            args_pp,\
                                            str(self.name))

class Wire(IR):
    _fields = ('name', 'width')
    def __str__(self, varmap=None):
        if varmap:
            return str(varmap[self.name])
        else:
            return str(self.name)

class UnaryOp(IR):
    _fields = ('op', 'A')
    def __str__(self, varmap=None):
        return '({} {})'.format(str(self.op), self.A.__str__(varmap))

class BinaryOp(IR):
    _fields = ('op', 'A', 'B')
    def __str__(self, varmap=None):
        return '({} {} {})'.format(str(self.op), self.A.__str__(varmap), \
                                                 self.B.__str__(varmap))

class Mux(IR):
    _fields = ('S', 'A', 'B')
    def __str__(self, varmap=None):
        return '(MUX {} {} {})'.format(self.S.__str__(varmap), \
                                       self.A.__str__(varmap), \
                                       self.B.__str__(varmap))

class Const(IR):
    _fields = ('number', 'width')
    def __str__(self, varmap=None):
        return '(CONST {} {})'.format(str(self.number), str(self.width))

class Memrd(IR):
    _fields = ('MEMID', 'ADDR')
    def __str__(self, varmap=None):
        return '(READ {} {})'.format(
                str(varmap[self.MEMID]) if varmap else str(self.MEMID), \
                self.ADDR.__str__(varmap))

class Memwr(IR):
    _fields = ('MEMID', 'ADDR', 'DATA', 'EN')
    def __str__(self, varmap=None):
        return '({} (WRITE {} {} {}))'.format(
                str(varmap[self.MEMID]) if varmap else str(self.MEMID), \
                self.ADDR.__str__(varmap), \
                self.DATA.__str__(varmap), \
                self.EN.__str__(varmap))

class Dff(IR):
    _fields = ('Q', 'D')
    def __str__(self, varmap=None):
        return '({} (:= {}))'.format(self.Q.__str__(varmap), \
                                     self.D.__str__(varmap))

class Connect(IR):
    _fields = ('Y', 'A')
    def __str__(self, varmap=None):
        return '({} (:= {}))'.format(self.Y.__str__(varmap), \
                                     self.A.__str__(varmap))

class Sel(IR):
    _fields = ('wire', 'low', 'high')
    def __str__(self, varmap=None):
        return '(SEL {} (SLICE {} {}))'.format(self.wire.__str__(varmap), \
                                               str(self.low), \
                                               str(self.high))

class Concat(IR):
    _fields = ('wires',)
    def __str__(self, varmap=None):
        return '(CONCAT (list {}))'.format(' '.join([w.__str__(varmap) for w in self.wires]))

def _demangle_name(name):
    #return name if '$memwr' in name else name[name.find('\\') + 1:]
    return name if '$' in name else name[name.find('\\') + 1:]

def _process_connections(connections, var, vid):

    def _process_bits(chunk):
        if not chunk.wire:
            return str(chunk.data)
        else:
            wire_name = _demangle_name(chunk.wire.name.str())
            sig_wire = Wire(wire_name, chunk.wire.width)
            #if wire_name not in var:
            #    var[wire_name] = vid
            #    vid += 1

            if chunk.offset == 0:
                return sig_wire
            else:
                return Sel(sig_wire, chunk.offset, chunk.offset)

    def _process_chunk(chunk, vid):
        if not chunk.wire:
            return Const(chunk.data, chunk.width), vid
        else:
            wire_name = _demangle_name(chunk.wire.name.str())
            sig_wire = Wire(wire_name, chunk.wire.width)
            #if wire_name not in var:
            #    print('--procchunk', wire_name)
            #    var[wire_name] = vid
            #    vid += 1

            if (chunk.width == chunk.wire.width) and (chunk.offset == 0):
                return sig_wire, vid
            elif chunk.width == 1:
                return Sel(sig_wire, chunk.offset, chunk.offset), vid
            else:
                return Sel(sig_wire, chunk.offset, \
                           chunk.offset + chunk.width - 1), vid

    exp = dict()
    for k,sig in connections.items():
        sigval = None
        signame = _demangle_name(k.str())
        if sig.is_wire():
            wire_name = _demangle_name(sig.as_wire().name.str())
            sigval = Wire(wire_name, sig.as_wire().width)
            if wire_name not in var:
                var[wire_name] = vid
                vid += 1
        elif sig.is_fully_const():
            sigval = sig.as_int()
            sigval = Const(sigval, sig.size())
        elif sig.is_chunk():
            sigval, vid = _process_chunk(sig.as_chunk(), vid)
        else:
            print('--procbits', signame, str(sig.to_sigbit_vector()))
            if sig.to_sigbit_vector():
                sigval = Concat([_process_bits(sigbits) \
                                 for sigbits in sig.to_sigbit_vector()])
            else:
                print("--> not wire or const!")
                sigval = str(sig)#sig.as_string()
        print('--procconn', signame, sigval) 
        exp[signame] = sigval
    return exp, vid


def rtlil_to_ir(vfile):
    design = ys.Design()
    top = vfile.split('.')[0]
    filext = vfile.split('.')[1]
    ys.run_pass("read_verilog " \
                + ("-sv " if filext == 'sv' else " ") \
                + vfile, design);
    ys.run_pass("hierarchy -check -top " + top, design)
    #ys.run_pass("memory -nomap " + top, design)
    ys.run_pass("proc", design) # processes ~~> dffs+muxes
    ys.run_pass("splice -wires", design) # add $slice and $concat cells
    ys.run_pass("debug flatten", design)
    ys.run_pass("pmuxtree", design)
    design.sort()
    ys.run_pass("write_rtlil", design)

    var = dict() # wire name -> id
    vid = 0
    decls = dict() # decl name -> Decl object
    defs = dict() # def name -> IR object
    stmts = dict() # def name -> IR object

    op_map = {
        '$add': 'ADD',
        '$and': 'AND',
        '$concat': 'CONCAT',
        '$eq': 'EQ',
        '$ge': 'GE',
        '$gt': 'GT',
        '$logic_and': 'LOGIC-AND',
        '$logic_not': 'LOGIC-NOT',
        '$logic_or': 'LOGIC-OR',
        '$le': 'LE',
        '$lt': 'LT',
        '$memrd': 'READ',
        '$mul': 'MULT',
        '$mux': 'MUX',
        '$nand': 'NAND',
        '$not': 'NOT',
        '$ne': 'NE',
        '$or': 'OR',
        '$reduce_bool': 'REDUCE-OR',
        '$reduce_or': 'REDUCE-OR',
        '$shl': 'SHL',
        '$shr': 'SHR',
        '$slice': 'SEL',
        '$sshr': 'SSHR',
        '$sub': 'SUB',
        '$xor': 'XOR',
    }

    # process all the wires, map names to integer ids, note attributes for declaring inputs, holes, memories
    for module in design.selected_whole_modules_warn():
        module.sort()
        for wire in module.selected_wires():
            name = _demangle_name(wire.name.str())
            #print(wire, name, wire.port_id, wire.port_input, wire.port_output, wire.attributes.keys())
            #print('--decl-----------------')
            port_type = ""
            if wire.port_input:
                port_type = "INPUT"
            if wire.port_output:
                port_type = "OUTPUT"
            if not port_type:
                # handle HOLE type
                hole_type = False
                hole_width = ""
                hole_params = ""
                for attr,val in wire.attributes.items():
                    attr_name = _demangle_name(attr.str())
                    print('--attr', attr_name)
                    if attr_name == 'hole_width':
                        hole_width = val.as_int(False)
                    if attr_name == 'hole_params':
                        hole_params = val.decode_string()
                        #hole_params = "(list \"{}\")".format(val.decode_string())
                        #print("attr: ", attr_name, decoded_val)
                    if hole_width and hole_params:
                        hole_type = True
                if hole_type:
                    decls[name] = Decl(name, "HOLE", [hole_width, hole_params], name)
                    var[name] = vid
                    vid += 1
                    continue
                else:
                    continue
            decls[name] = Decl(name, port_type, [wire.width], name)
            var[name] = vid
            vid += 1
        for mem_id, mem in module.memories.items():
            name = _demangle_name(mem.name.str())
            decls[name] = Decl(name, "MEMORY", [mem.width, mem.size], name)
            var[name] = vid
            vid += 1

    for module in design.selected_whole_modules_warn():
        for cell in module.selected_cells():
            if cell.type.str() == '$dff':
                conn, vid = _process_connections(cell.connections_, var, vid)
                w = None
                for k,p in cell.parameters.items():
                    if _demangle_name(k.str()) == 'WIDTH':
                        w = p.as_int()
                #n = [k for k,i in var.items() if (i == conn['Q'])][0]
                n = conn['Q']
                if '$memwr' in str(n):
                    # don't add decl for intermediate generated memwr regs
                    continue
                decls[n.name] = Decl(n, "REGISTER", [w, "0"], n)
                stmts[n.name] = Dff(n, conn['D'])
                print('--dff', decls[n.name])
            elif '$memwr' in cell.type.str():
                print(cell)
                conn, vid = _process_connections(cell.connections_, var, vid)
                m = None
                for k,p in cell.parameters.items():
                    if _demangle_name(k.str()) == 'MEMID':
                        m = _demangle_name(p.decode_string())
                stmts[m] = Memwr(m, conn['ADDR'], conn['DATA'], conn['EN'])

    terminals = list(decls.keys())
    print("TERMINALS", terminals)

    # iterate through all cell and connections to generate "defs" map,
    # mapping var names to IR objects.
    # connections
    for module in design.selected_whole_modules_warn():
        for connect in module.connections_:
            if connect[0].is_wire() and connect[1].is_wire():
                # XXX: consider keys to be IR.str
                # I think they'll still be unique???
                #print("def name", _demangle_name(connect[0].as_wire().name.str()))
                #defs[_demangle_name(connect[0].as_wire().name.str())] = \
                defs[str(Wire(_demangle_name(connect[0].as_wire().name.str()),\
                              connect[0].as_wire().width))] = \
                        Wire(_demangle_name(connect[1].as_wire().name.str()), \
                             connect[1].as_wire().width)
    # cells
    for module in design.selected_whole_modules_warn():
        for cell in module.selected_cells():
            print(cell)
            if not cell.type.str() in op_map.keys():
                continue
            op = op_map[cell.type.str()]
            conn, vid = _process_connections(cell.connections_, var, vid)
            if op in ('READ'):
                memid = None
                for k,p in cell.parameters.items():
                    if _demangle_name(k.str()) == 'MEMID':
                        memid = _demangle_name(p.decode_string())
                        #memid = var[_demangle_name(p.decode_string())]
                        break
                defs[str(conn['DATA'])] = Memrd(memid, conn['ADDR'])
                #defs[conn['DATA'].name] = Memrd(memid, conn['ADDR'])
            if op in ('ADD', 'AND', 'EQ', 'GE', 'GT', 'LOGIC-AND', 'LOGIC-OR', \
                      'LE', 'LT', 'MULT', 'NAND', 'NE', 'OR', 'SHL', 'SHR', \
                      'SSHR', 'SUB', 'XOR'):
                print("--Y bi", str(conn['Y']))
                if isinstance(conn['Y'], Sel):
                    if str(conn['Y'].wire.name) not in var.keys():
                        print('add stmt')
                        #defs[str(conn['Y'].wire)] = conn['Y'].wire
                        #stmts[conn['Y'].wire.name] = Connect(conn['Y'].wire, Const(0, conn['Y'].wire.width))
                        #terminals.append(conn['Y'].wire.name)
                        #var[conn['Y'].wire.name] = vid
                        #vid += 1
                defs[str(conn['Y'])] = BinaryOp(op, conn['A'], conn['B'])
                #defs[conn['Y'].name] = BinaryOp(op, conn['A'], conn['B'])
            elif op in ('LOGIC-NOT', 'NOT', 'REDUCE-OR'):
                print("--Y un", str(conn['Y']))
                defs[str(conn['Y'])] = UnaryOp(op, conn['A'])
                #defs[conn['Y'].name] = UnaryOp(op, conn['A'])
                if isinstance(conn['Y'], Sel):
                    if str(conn['Y'].wire.name) not in var:
                        print('add stmt')
                        #defs[str(conn['Y'].wire)] = conn['Y'].wire
                        #stmts[conn['Y'].wire.name] = Connect(conn['Y'].wire, Const(0, conn['Y'].wire.width))
                        #terminals.append(conn['Y'].wire.name)
                        #var[conn['Y'].wire.name] = vid
                        #vid += 1
            elif op in ('MUX'):
                print("--Y mux", conn['Y'])
                defs[str(conn['Y'])] = Mux(conn['S'], conn['A'], conn['B'])
                #defs[conn['Y'].name] = Mux(conn['S'], conn['A'], conn['B'])
            elif op in ('SEL'):
                slice_begin = None
                slice_end = None
                for k,p in cell.parameters.items():
                    if _demangle_name(k.str()) == 'OFFSET':
                        slice_begin = p.as_int()
                    elif _demangle_name(k.str()) == 'Y_WIDTH':
                        slice_end = p.as_int()
                print("--Y sel", conn['Y'])
                if str(conn['A']) not in (list(defs.keys()) + terminals):
                    print("--!A sel", conn['A'])
                defs[str(conn['Y'])] = Sel(conn['A'], slice_begin, \
                                           (slice_begin + slice_end) - 1)
            elif op in ('CONCAT'):
                print("--Y concat", conn['Y'])
                A = conn['A']
                if isinstance(A, Sel):
                    if str(A.wire.name) not in var:
                        print('A concat no thar')
                        A = Wire(str(A), '')
                B = conn['B']
                if isinstance(B, Sel):
                    if str(B.wire.name) not in var:
                        print('B concat no thar')
                        B = Wire(str(B), '')
                defs[str(conn['Y'])] = Concat([B, A])

    def _unfold_logic(exp, defs, terminals, T='-->'):
        # if exp is const or it's a wire with name in terminals, then done
        #print(T, exp)
        if isinstance(exp, Const):
            return exp
        elif isinstance(exp, Wire) and exp.name in terminals:
            #print(T, "terminal")
            return exp
        # else, match on other IR types with recursive calls for each arg
        elif isinstance(exp, Wire):
            return _unfold_logic(defs[str(exp)], defs, terminals, '  '+T)
            #return _unfold_logic(defs[exp.name], defs, terminals)
        elif isinstance(exp, UnaryOp):
            return UnaryOp(exp.op, _unfold_logic(exp.A, defs, terminals, '  '+T))
        elif isinstance(exp, BinaryOp):
            return BinaryOp(exp.op, _unfold_logic(exp.A, defs, terminals, '  '+T), \
                                    _unfold_logic(exp.B, defs, terminals, '  '+T))
        elif isinstance(exp, Mux):
            return Mux(_unfold_logic(exp.S, defs, terminals, '  '+T), \
                       _unfold_logic(exp.A, defs, terminals, '  '+T), \
                       _unfold_logic(exp.B, defs, terminals, '  '+T))
        elif isinstance(exp, Memrd):
            return Memrd(_unfold_logic(exp.MEMID, defs, terminals, '  '+T), \
                         _unfold_logic(exp.ADDR, defs, terminals, '  '+T))
        elif isinstance(exp, Sel):
            return Sel(_unfold_logic(exp.wire, defs, terminals, '  '+T), \
                       exp.low, exp.high)
        elif isinstance(exp, Concat):
            return Concat([_unfold_logic(x, defs, terminals, '  '+T) for x in exp.wires])
        elif str(exp) in terminals:
            return exp
        print("  DID I ERR?", exp, type(exp))
        return exp

    # for each var in hole params, create intermediate wire definition and add to stmts
    #print(_unfold_logic(defs['op'], defs, terminals))
    hparams = []
    for name, decl in decls.items():
        if decl.port_type == "HOLE" and len(decl.args) > 1 and decl.args[1]:
            hparams += decl.args[1].split(' ')
    hparams = list(set(hparams))
    print('--hparams', hparams)
    for p in hparams:
        if p not in var:
            var[p] = vid
            vid += 1
        stmts[p] = Connect(Wire(p, ""), _unfold_logic(defs[p], defs, terminals))
    
    # starting from $memwr, go backwards until terminals
    for name, mw in stmts.items():
        if isinstance(mw, Memwr):
            print("mw.ADDR", mw.ADDR)
            stmts[name] = Memwr(mw.MEMID, \
                                    _unfold_logic(mw.ADDR, defs, terminals), \
                                    _unfold_logic(mw.DATA, defs, terminals), \
                                    _unfold_logic(mw.EN, defs, terminals))

    # starting from $dff.Q, go backwards and build $dff.D until terminals
    for name, dff in stmts.items():
        if isinstance(dff, Dff):
            print("--reg", dff)
            stmts[name] = Dff(dff.Q, _unfold_logic(dff.D, defs, terminals))

    ## drive Outputs
    for name, decl in decls.items():
        if decl.port_type == "OUTPUT":
            if name in defs:
                #print("decl in defs", name, defs[name])
                stmts[name] = Connect(Wire(name, decl.args[0]), _unfold_logic(defs[name], defs, terminals))


    stmts_ordered = []
    for n, x in stmts.items():
        if isinstance(x, Connect):
            stmts_ordered.append(x)
    for n, x in stmts.items():
        if isinstance(x, Memwr):
            stmts_ordered.append(x)
    for n, x in stmts.items():
        if isinstance(x, Dff):
            stmts_ordered.append(x)

    return "(define-block {}\n(decl\n  {})\n(stmt\n  {}))".format(\
                top,\
                "\n  ".join([x.__str__(var) for x in decls.values()]),\
                "\n  ".join([x.__str__(var) for x in stmts_ordered]))
                #"\n  ".join([x.__str__() for x in decls.values()]),\
                #"\n  ".join([x.__str__() for x in stmts_ordered]))

if __name__ == "__main__":
    print(rtlil_to_ir("acc_holes.v"))
