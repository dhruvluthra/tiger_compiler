signature REG_ALLOC =
sig
  structure Frame : FRAME
  type allocation

  val alloc : Assem.instr list * bool  ->
                  Assem.instr list * allocation
end

structure RegAlloc : REG_ALLOC =
struct
  structure Frame = MipsFrame
  structure Set = IntBinarySet
  structure Table = IntMapTable(type key = int
                                fun getInt k = k)

  type allocation = Frame.register Temp.Table.table

  fun printAllocTable table =
    let
      val tableList = Table.listItemsi table
      fun print_table_items [] = ()
        | print_table_items ((key, value)::l) =
          ((print("Temporary Register: " ^ Temp.makestring key ^ " Allocated Register: " ^ (case Temp.Table.look(table, key) of
                                                                                               SOME(reg) => reg
                                                                                              | NONE => "register not allocated") ^ "\n"));
             print_table_items(l))
    in
      print_table_items tableList
    end

  fun alloc (instrs, debug) =
      let
          val cfgraph = MakeGraph.instrs2graph instrs
          val (igraph, live_out_table) = Liveness.interferenceGraph cfgraph
          val (final_alloc, spill_list) = Color.color {interference=igraph,
                                                      initial=Frame.tempMap,
                                                      registers=Frame.registers}
      in
          (if debug
           then (MakeGraph.printCFGraph cfgraph; Liveness.printIGraph igraph; printAllocTable final_alloc)
           else ();
           (instrs, final_alloc))
      end

end
