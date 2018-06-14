signature COLOR =
sig
  structure Frame : FRAME
  structure Graph : FUNCGRAPH
  type allocation

  val color : {interference: Liveness.nodedata Graph.graph,
               initial: allocation,
               registers: Frame.register list}
              -> allocation * Temp.temp list
end

structure Color : COLOR =
struct

    structure Frame = MipsFrame
    structure Graph = MakeGraph.Graph
(* structure RegSet = SplaySetFn(struct type ord_key = Frame.register
                                  val compare = String.compare
                                  end) *)
    structure E = ErrorMsg

    type allocation = Frame.register Temp.Table.table

    fun get_spill_cost n = 1 (* TODO: EXTRA CREDIT *)

    (* Make set structure that compares based on spillcost *)
    fun compare_nodes (nodeid1, nodeid2) =
          Int.compare(get_spill_cost nodeid1, get_spill_cost nodeid2)
    structure NodeSet = SplaySetFn(struct type ord_key = MakeGraph.Graph.nodeID
                                val compare = compare_nodes
                                end)

    fun color {interference, initial, registers} =
        let
            val k = List.length registers

            (* MAKE SIMPLIFY LIST AND SPILL SET *)
            fun make_worklists (node, (simplify_list, spill_set)) =
                let
                    val register = Graph.getNodeID(node)
                in
                    case Temp.Table.look(initial, register) of
                        (* precolored register --> do nothing *)
                        SOME(n) => (simplify_list, spill_set)
                      | NONE => if List.length(Graph.preds(node)) >= k
                                (* Non-trivial node --> add to spill set *)
                                then (simplify_list, NodeSet.add(spill_set, register))
                                (* Trivial node --> add to simplify list *)
                                else (register::simplify_list, spill_set)
                end
            val (simplify_list, spill_set) =
                    foldl make_worklists ([], NodeSet.empty) (Graph.nodes(interference))

            (* BUILD STACK *)
            (* Remove node from graph and add to stack *)
            fun simplify (node, stack, graph) = ((node, graph)::stack, Graph.removeNode(graph, node))

            (* Add node with lowest spill cost to simplify list *)
            fun spill (spill_set, simplify_list) =
                let
                    val spill_ordered_by_cost = NodeSet.listItems spill_set
                    val lowestcost = List.hd spill_ordered_by_cost
                in
                    (NodeSet.delete(spill_set, lowestcost), lowestcost::simplify_list)
                end

            fun build_stack (simplify_list, spill_set, stack, graph) =
                case simplify_list of
                    [] => if NodeSet.isEmpty(spill_set)
                          then stack
                      (*  else (let val (new_spill, new_simplify) = spill(spill_set, simplify_list)
                                in build_stack(new_simplify, new_spill, stack, graph)
                                end) *)
                          else (let
                                  val (new_simplify_list, new_spill_set) = foldl make_worklists ([], NodeSet.empty) (Graph.nodes(graph))
                                  val (new_spill, new_simplify) = spill(spill_set, simplify_list)
                                in
                                  if List.null new_simplify_list
                                  then build_stack(new_simplify, new_spill, stack, graph)
                                  else build_stack(new_simplify_list, new_spill_set, stack, graph)
                                end)
                  | n::new_simplify =>
                      let val (new_stack, new_graph) = simplify(n, stack, graph)
                      in build_stack(new_simplify, spill_set, new_stack, new_graph)
                      end
            val stack = build_stack (simplify_list, spill_set, [], interference)


            (* ASSIGN COLORS *)

            fun assign_colors (stack, alloc) =
                case stack of
                    [] => alloc
                  | (nodeId, graph)::new_stack =>
                      let
                          (*val register_set = RegSet.addList(RegSet.empty, registers)*)
                          val register_list = registers

                          fun delete (item, []) = []
                            | delete (item, a::l) = if item = a then delete(item, l)
                                                    else a::delete(item,l)

                          (* Get set of registers that node can be assigned *)
                          fun remove_register (nodeid, reg_list) =
                              case Temp.Table.look(alloc, nodeid) of
                                  SOME(reg) => delete(reg, reg_list)
                                              (*RegSet.difference(reg_set, RegSet.add(RegSet.empty, reg))*)
                                | NONE => reg_list
                          val remaining_colors =
                                Graph.foldSuccs remove_register register_list (Graph.getNode(graph, nodeId))

                      in
                          if List.null(remaining_colors)
                          then (E.error 0 "Not enough registers available. Could not compile program.";
                                assign_colors(new_stack, alloc) )
                              (* Pick random (first) reg from remaining set and add to alloc *)
                          else (let val reg = List.hd remaining_colors
                                in assign_colors(new_stack, Temp.Table.enter(alloc, nodeId, reg))
                                end)
                      end
            val alloc = assign_colors(stack, initial)
            val spill_list = []
        in
          (alloc, spill_list)
        end

end
