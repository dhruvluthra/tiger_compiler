structure Main = struct

  structure Tr = Translate
  structure F = Frame
  structure A = Assem
  structure R = RegAlloc

  val DEBUG = false

  fun getsome (SOME x) = x
    | getsome _ = ErrorMsg.impossible "Argument must be SOME option"

  fun formatdata (fd, F.PROC{body,frame}) = ()
    | formatdata (fd, F.STRING(lab,s)) =
        let
            val lenword = Int.toString(String.size(s))
        in
          (TextIO.output (fd, ".align 2 \n");
           TextIO.output (fd, (Symbol.name lab) ^ ": .word " ^ lenword ^ "\n");
           TextIO.output (fd, ".ascii \"" ^ s ^ "\"\n"))
        end




  fun emitproc out (F.PROC{body,frame}, fragCount) =
        let val stms = Canon.linearize body
            val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
            val instrs = List.concat(map (MipsGen.codegen frame) stms')
            val instrs' = if fragCount = 1
                          then F.procEntryExit2 instrs
                          else F.procEntryExit2 instrs
            val format0 = Assem.format(Temp.makestring)
        in
            (if DEBUG
             then (print ("====== Fragment " ^ (Symbol.name (Frame.name frame)) ^ " =====\n");
                   (* print ("-------- IR Tree --------\n");
                   Printtree.printtree(out,body); *)
                   (* print ("----- Canonical Tree -----\n");
                   app (fn s => Printtree.printtree(out,s)) stms; *)
                   print ("------ Infinite Temp Machine Code ------\n");
                   app (fn i => TextIO.output(out,format0 i)) instrs')
              else ();
              instrs')
        end
    | emitproc out (F.STRING(lab,s), fragCount) =
          (if DEBUG
           then (print ("====== Fragment " ^ (Symbol.name (lab)) ^ " ======\n");
                TextIO.output(out,F.string(lab,s)))
           else ();
           [])


  fun withOpenFile fname f =
    let val out = TextIO.openOut fname
        val instrslst = f out before TextIO.closeOut out
    in
        (instrslst)
        handle e => (TextIO.closeOut out; raise e)
    end

  fun compile filename =
    let val _ = print ("============= Syntax Errors =============\n")
        val forMipsName = List.hd (String.tokens (fn c => c = #".") filename)
        val absyn = Parse.parse filename
        val _ = print ("============== Type Errors ==============\n")
        val frags = (FindEscape.findEscape absyn; Semant.transProg absyn)
        fun processfrag (frag, (allinstrs, fragCount)) =
            let
              val fraginstrs = emitproc TextIO.stdOut (frag, fragCount)
            in
                (fraginstrs @ allinstrs, fragCount+1)
            end
        val (fullinstrslist,fragCount) = foldr processfrag ([],1) frags
        val (instrs, final_alloc) = R.alloc (fullinstrslist, DEBUG)
        fun temp_look_up temp = case Temp.Table.look(final_alloc, temp) of
                                  SOME(reg) => reg
                                | NONE      => Temp.makestring temp
        val format0 = Assem.format(temp_look_up)

        val fd = TextIO.openOut (forMipsName ^ ".s")
    in
        (TextIO.output(fd, ".text \n");
         TextIO.output(fd, "\n");
         TextIO.output(fd, ".globl main\n");
         TextIO.output(fd, "main: \n");
         app (fn i => TextIO.output(fd, (format0 i))) instrs;
         TextIO.output (fd, ".data \n");
         app (fn frag => formatdata(fd, frag)) frags;
         TextIO.closeOut fd;
         fullinstrslist)
    end

end
