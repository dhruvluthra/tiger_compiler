structure Liveness :
  sig
    structure Graph : FUNCGRAPH
    structure Set : ORD_SET
    structure Table : TABLE
    type nodedata
    val interferenceGraph : MakeGraph.nodedata Graph.graph -> nodedata Graph.graph * Set.set Table.table
    val printLiveOutTable : Set.set Table.table -> unit
    val printIGraph : nodedata Graph.graph  -> unit
  end

=
struct

  structure Graph = MakeGraph.Graph
  type nodedata = int
  structure Set = IntBinarySet
  structure Table = IntMapTable(type key = Graph.nodeID
                                fun getInt k = k)

  structure E = ErrorMsg

  fun printLiveOutTable table =
      let
        val table_items = Table.listItemsi table
        fun print_table_items [] = ()
          | print_table_items ((key, value)::l) =
           (let
              fun listToString [] = ""
               |  listToString (a::l) = Int.toString a ^ ", " ^ listToString(l)
            in
              (print("nodeID : " ^ Int.toString key ^ " liveOutTemps: " ^ listToString (Set.listItems value) ^ "\n");
               print_table_items(l))
            end)
      in
        print_table_items table_items
      end

  fun printIGraph igraph =
              Graph.printGraph (fn (id, ndata) => "TEMP " ^ Int.toString id) igraph

  fun livenessAnalysis (graph, [], visited, 0, live_in_table, live_out_table) = (live_in_table, live_out_table)
    | livenessAnalysis (graph, [], visited, x, live_in_table, live_out_table) =
              livenessAnalysis(graph, Graph.nodes graph, Set.empty, 0, live_in_table, live_out_table)
    | livenessAnalysis (graph, a::l, visited, x, live_in_table, live_out_table) =
            let
              val curr_node = a
              val nodeID = Graph.getNodeID(curr_node)
              val live_out_prev = case Table.look(live_out_table, nodeID) of
                                    SOME(set) => set
                                  | NONE      => Set.empty
              val live_in_prev = case Table.look(live_in_table, nodeID) of
                                    SOME(set) => set
                                  | NONE      => Set.empty
              val predecessors = Graph.preds(curr_node)
              fun build_live_out (succ_id, set) =
                  let
                    val live_in_succ = case Table.look(live_in_table, succ_id) of
                                          SOME(set) => set
                                        | NONE      => Set.empty
                  in
                    Set.union(set, live_in_succ)
                  end
              val live_out_set = Graph.foldSuccs build_live_out Set.empty curr_node
              val {def=def, use=use, ismove, assem} = Graph.getNodeData(curr_node)
              val live_in_set = Set.union(use, Set.difference(live_out_set, def))
              val live_out_table_new = Table.enter(live_out_table, nodeID, live_out_set)
              val live_in_table_new = Table.enter(live_in_table, nodeID, live_in_set)
              val sets_changed = case Set.equal(live_in_prev, live_in_set) andalso Set.equal(live_out_prev, live_out_set) of
                                    true  => 0
                                  | false => 1
            in
              livenessAnalysis(graph, l, Set.add(visited, nodeID), x+sets_changed, live_in_table_new, live_out_table_new)
            end

  fun build_i_graph (igraph, cgraph, visited, [], live_out_table) = igraph
    | build_i_graph (igraph, cgraph, visited, a::l , live_out_table) =
      let
        val curr_node = a
        val nodeID = Graph.getNodeID(curr_node)
        val {def=def, use=use, ismove=ismove, assem} = Graph.getNodeData(curr_node)
        fun add_temp_igraph (tempID, igraph) =  case Graph.getNode'(igraph, tempID) of
                                          SOME node => igraph
                                        | NONE      => Graph.addNode(igraph, tempID, tempID)
        val igraph_def = Set.foldl add_temp_igraph igraph def
        val live_out = case Table.look(live_out_table, nodeID) of
                              SOME(set) => set
                            | NONE      => Set.empty
        val igraph_live_out = Set.foldl add_temp_igraph igraph_def live_out

        fun add_edges_def (defID, igraph) =
            let
              fun add_edge_live_out(tempID, igraph') = if tempID = defID
                                                       then igraph'
                                                       else Graph.doubleEdge(igraph', defID, tempID, false)
            in
              Set.foldl add_edge_live_out igraph live_out
            end
        val igraph_edges = Set.foldl add_edges_def igraph_live_out def
        val igraph_use = Set.foldl add_temp_igraph igraph_edges use
        fun add_move_edge (d::l1, s::l2, igraph) = Graph.doubleEdge(igraph, d, s, true)
          | add_move_edge (d, s, igraph) = (E.error 0 "Move statement cannot have multiple use or defs"; igraph)
        val igraph_move_edges = if ismove
                                then add_move_edge(Set.listItems(def), Set.listItems(use), igraph_use)
                                else igraph_edges

        val predecessors = Graph.preds(curr_node)
    (*  fun add_to_queue(pred_nodeID, l) =
            let
              val pred_node = Graph.getNode(cgraph, pred_nodeID)
            in
              l @ [pred_node]
            end
        val queue = foldl add_to_queue l predecessors *)
      in
        build_i_graph(igraph_move_edges, cgraph, Set.add(visited, nodeID), l, live_out_table)
      end


  fun interferenceGraph control_graph =
      let
        val end_node = Graph.getNode(control_graph, 0)
        val live_in_table_init = Table.empty
        val live_out_table_init = Table.empty
        val (live_in, live_out) = livenessAnalysis(control_graph, Graph.nodes control_graph, Set.empty, 0, live_in_table_init, live_out_table_init)
        val interference_graph = build_i_graph (Graph.empty, control_graph, Set.empty, Graph.nodes control_graph, live_out)
      in
        (interference_graph, live_out)
      end

end
