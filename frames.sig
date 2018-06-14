signature FRAME =
sig type frame
    type access
    datatype frag = PROC of {body:Tree.stm, frame:frame}
                  | STRING of Temp.label * string

    type register = string

    val FP : Temp.temp
    val SP : Temp.temp
    val RA : Temp.temp
    val RV : Temp.temp
    val R0 : Temp.temp
    val specialregs : (Temp.temp * register) list
    val argregs : (Temp.temp * register) list
    val calleesaves : (Temp.temp * register) list
    val callersaves : (Temp.temp * register) list
    val get_registers : (Temp.temp * register) list -> Temp.temp list
    val registers : register list

    val newFrame : {name: Temp.label, formals: bool list} -> frame
    val name : frame -> Temp.label
    val formals : frame -> access list
    val allocLocal : frame -> bool -> access
    val wordSize : int
    val exp : access -> Tree.exp -> Tree.exp
    val externalCall : (string * Tree.exp list) -> Tree.exp
    val string : (Temp.label * string) -> string
    val tempMap: register Temp.Table.table

    val printAccesses : access list -> unit

    val procEntryExit1  : frame * Tree.exp -> Tree.exp * int * int * int
    val procEntryExit2  : Assem.instr list -> Assem.instr list
    val procEntryExit2' : Assem.instr list -> Assem.instr list
    val procEntryExit3  : frame * Assem.instr list -> {prolog: string, body: Assem.instr list, epilog: string}

end
