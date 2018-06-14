structure MakeGraph :
  sig
      structure Graph : FUNCGRAPH
      structure Set : ORD_SET
      type nodedata
      val instrs2graph : Assem.instr list -> nodedata Graph.graph
      val printCFGraph : nodedata Graph.graph  -> unit
  end
=
struct
    structure Graph = FuncGraph(struct type ord_key = int
                                val compare = Int.compare
                                end)

    structure Set = IntBinarySet
    structure E = ErrorMsg
    structure S = Symbol

    type nodedata = {def: Set.set,
                     use: Set.set,
                     ismove: bool,
                     assem: string}

    structure Table = IntMapTable(type key = Temp.label
  				                        fun getInt(s,n) = n)

    fun printCFGraph graph =
        let
            fun setToString set =
              let
                val list = Set.listItems set
                fun listToString [] = ""
                 |  listToString (a::l) = Int.toString a ^ ", " ^ listToString(l)
              in
                listToString list
              end
         in
            Graph.printGraph (fn (id, {def, use, ismove, assem}) => Int.toString(id) ^ ": " ^ assem ^ "defs: " ^ setToString(def) ^ "use: " ^ setToString(use)) graph
         end

    fun addEdges (instr, (graph, curr_node, label_start_table, label_end_table)) =
        case instr of
            Assem.OPER{assem, dst, src, jump} => (* jal --> add edge from curr to start and from end to curr-1
                                                    j --> add edge from curr to j label start
                                                    jr --> do nothing
                                                    else --> add edge curr_node -1 *)
            (  case jump of
                  SOME(jump_lst) =>
                      (case jump_lst of
                          [] => (graph, curr_node+1, label_start_table, label_end_table)
                        | _  => let
                                  fun add_label_start_edges (label, graph) =
                                        case Table.look(label_start_table, label) of
                                              SOME(n) => Graph.addEdge(graph,
                                                                    {from=curr_node, to=n, isMoveEdge=false})
                                            | NONE    => ((*E.error 0 ("Label start table should have all labels: " ^ S.name label);*) graph)
                                  val graph_with_start_edges = foldl add_label_start_edges graph jump_lst
                                  fun add_label_end_edges (label, graph) =
                                        case Table.look(label_end_table, label) of
                                              SOME(n) => Graph.addEdge(graph,
                                                                    {from=n, to=curr_node-1, isMoveEdge=false})
                                            | NONE    => (E.error 0 ("Label end table should have all labels: " ^ S.name label); graph_with_start_edges)
                                  val graph_jal = Graph.addEdge(graph, {from=curr_node, to=curr_node-1, isMoveEdge=false})
                                  val graph_with_end_edges = if String.isPrefix "jal" assem
                                                             then graph_jal
                                                             else graph_with_start_edges

                                in
                                  (graph_with_end_edges, curr_node+1, label_start_table, label_end_table)
                                end )

                | NONE           => let
                                      val graph_with_edge = Graph.addEdge(graph,
                                                            {from=curr_node, to=curr_node-1, isMoveEdge=false})
                                    in
                                      (graph_with_edge, curr_node+1, label_start_table, label_end_table)
                                    end )
          | _ => (* Add edge to curr_node-1 *)
              let
                val graph_with_edge = Graph.addEdge(graph,
                                                    {from=curr_node, to=curr_node-1, isMoveEdge=false})
              in
                (graph_with_edge, curr_node+1, label_start_table, label_end_table)
              end


    fun addNodes (instr, (graph, curr_node, label_start_table, label_end_table, curr_labels)) =
        case instr of
            Assem.OPER{assem, dst, src, jump} => (* Create node. jr -> save all curr labels in end table + clear curr_labels *)
                let
                    val graph_with_node =
                          Graph.addNode(graph,
                                        curr_node,
                                        {def=Set.addList(Set.empty, dst), use=Set.addList(Set.empty, src), ismove=false, assem=assem})
                in
                    if String.isPrefix "jr" assem
                    then (graph_with_node,
                          curr_node-1,
                          label_start_table,
                          foldl (fn (l, table) => Table.enter(table, l, curr_node)) label_end_table curr_labels,
                          [])
                    else (graph_with_node,
                          curr_node-1,
                          label_start_table,
                          label_end_table,
                          curr_labels)
                end

          | Assem.LABEL{assem, lab} =>   (*Create node. Add to curr labels and add to start table *)
                (Graph.addNode(graph,
                               curr_node,
                               {def=Set.empty, use=Set.empty, ismove=false, assem=assem}),
                 curr_node-1,
                 Table.enter(label_start_table, lab, curr_node),
                 label_end_table,
                 lab::curr_labels)

          | Assem.MOVE{assem, dst, src} => (* Create node *)
                (Graph.addNode(graph,
                               curr_node,
                               {def=Set.add(Set.empty, dst), use=Set.add(Set.empty, src), ismove=true, assem=assem}),
                 curr_node-1,
                 label_start_table,
                 label_end_table,
                 curr_labels)



    fun instrs2graph instrs =
        let
            val init_graph: nodedata Graph.graph = Graph.addNode(Graph.empty, 0, {def=Set.empty, use=Set.empty, ismove=false, assem="End node"})
            val (graph_with_nodes, _, label_start_table, label_end_table, _) =
                  foldl addNodes (init_graph, List.length instrs, Table.empty, Table.empty, []) instrs

            val (final_graph, _, _, _) =
                  foldr addEdges (graph_with_nodes, 1, label_start_table, label_end_table) instrs
        in
            final_graph
        end



end
