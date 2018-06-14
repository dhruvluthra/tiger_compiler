structure FindEscape: sig val findEscape: Absyn.exp -> unit
                      end =
struct

    structure A = Absyn

    type depth = int
    type escEnv = (depth * bool ref) Symbol.table

    fun traverseVar (env:escEnv, d:depth) =
        let fun trvar (A.SimpleVar(id, pos)) =
                  (case Symbol.look(env, id) of
                      SOME((def_d, bool_ref)) =>
                          (if d > def_d
                           then bool_ref := true
                           else ())
                    | NONE => ())
              | trvar (A.FieldVar(var, id, pos)) = trvar var
              | trvar (A.SubscriptVar(var, index_exp, pos)) =
                  (trvar var;
                   traverseExp(env, d) index_exp)
        in
            trvar
        end

    and traverseExp (env:escEnv, d:depth) =
        let fun trexp (A.VarExp(v)) = traverseVar(env, d) v
              | trexp (A.CallExp{func, args, pos}) =
                    let fun process_args [] = ()
                          | process_args (arg_exp::arg_list) =
                              (trexp arg_exp;
                               process_args arg_list)
                    in
                        process_args args
                    end
              | trexp (A.OpExp{left, oper, right, pos}) =
                    (trexp left;
                     trexp right)
              | trexp (A.RecordExp{fields, typ, pos}) =
                    let fun process_fields [] = ()
                          | process_fields ((symbol, exp, pos)::field_list) =
                              (trexp exp;
                               process_fields(field_list))
                    in
                        process_fields(fields)
                    end
              | trexp (A.SeqExp(seq)) =
                    let fun process_seq [] = ()
                          | process_seq ((exp, pos)::seq) =
                              (trexp exp;
                               process_seq(seq))
                    in
                        process_seq(seq)
                    end
              | trexp (A.AssignExp{var, exp, pos}) =
                    (traverseVar(env, d) var;
                     trexp exp)
              | trexp (A.IfExp{test, then', else'=NONE, pos}) =
                    (trexp test;
                     trexp then')
              | trexp (A.IfExp{test, then', else'=SOME(e), pos}) =
                    (trexp test;
                     trexp then';
                     trexp e)
              | trexp (A.WhileExp{test, body, pos}) =
                    (trexp test;
                     trexp body)
              | trexp (A.ForExp{var, escape, lo, hi, body, pos}) =
                    let
                        val loop_env = traverseDecs(env, d) (A.VarDec{name=var, escape=escape, typ=NONE, init=lo, pos=pos})
                    in
                        (trexp lo;
                         trexp hi;
                         traverseExp(loop_env, d) body)
                    end
              | trexp (A.LetExp{decs, body, pos}) =
                    let
                        fun add_dec (dec, env) = traverseDecs(env, d) dec
                        val body_env = foldl add_dec env decs
                    in
                        traverseExp(body_env, d) body
                    end
              | trexp (A.ArrayExp{typ, size, init, pos}) =
                    (trexp size;
                     trexp init)
              | trexp (_) = () (* NilExp,  IntExp, StringExp, BreakExp *)
        in
            trexp
        end

    and traverseDecs (env:escEnv, d:depth) =
        let fun trdec (A.VarDec{name, escape, typ, init, pos}) =
                    (escape := false;
                     Symbol.enter(env, name, (d, escape)))
              | trdec (A.TypeDec(decs)) = env
              | trdec (A.FunctionDec(fundecs)) =
                  let val new_depth = d+1 (* Function-nesting depth is incremented *)
                      fun process_decs [] = ()
                        | process_decs ({name, params, result, body, pos}::decs) =
                            let fun add_param ({name, escape, typ, pos}, env) =
                                    (escape := false;
                                     Symbol.enter(env, name, (new_depth, escape)))
                                val fun_env = foldl add_param env params
                            in
                                (traverseExp(fun_env, new_depth) body;
                                 process_decs decs)
                            end
                  in
                      (process_decs fundecs;
                       env)
                  end
        in
            trdec
        end


    fun findEscape(prog: Absyn.exp) : unit =
        let
            val init_env: escEnv = Symbol.empty
            val init_depth: depth = 0
        in
            traverseExp(init_env, init_depth) prog
        end

end
