#use "semantic-analyser.ml";;

(* module type CODE_GEN = sig
   val make_consts_tbl : expr' list -> (constant * ('a * string)) list
   val make_fvars_tbl : expr' list -> (string * 'a) list
   val generate : (constant * ('a * string)) list -> (string * 'a) list -> expr' -> string
   end;; *)

module Code_Gen : sig
  val make_consts_tbl : expr' list -> (constant * int * string) list
  val make_fvars_tbl : expr' list -> (string * int) list
  val generate : (constant * int * string) list -> (string * int) list -> int -> expr' -> string
end = struct
  let sizeOfVoid = 1
  and sizeOfNil = 1
  and sizeOfChar = 1 + 1
  and sizeOfBool = 1 + 1
  and sizeOfInt = 1 + 8
  and sizeOfFloat = 1 + 8
  and sizeOfSymbol = 1 + 8
  and sizeOfPair = 1 + 8 + 8
  and sizeOfClosure = 1 + 8 + 8
  and sizeOfLongSOB = function
    | Vector lst -> 1 + 8 + (8 * List.length lst)
    | String st -> 1 + 8 + String.length st
    | _ -> raise X_syntax_error

  let rec collectConsts expr' constLst =
    match expr' with
    | Seq' bodies|Or' bodies ->
      List.fold_right (fun expr' lst -> collectConsts expr' constLst @ lst) bodies constLst
    | If' (test, dit, dif) ->
      collectConsts test constLst @ collectConsts dit constLst @ collectConsts dif constLst
    | Def' (expr1', expr2') ->
      collectConsts expr1' constLst @ collectConsts expr2' constLst
    | Applic' (expr', expr'List)|ApplicTP' (expr', expr'List) ->
      List.fold_right (fun expr' lst -> lst @ collectConsts expr' constLst) expr'List constLst @ collectConsts expr' constLst
    | LambdaSimple' (paramsArr, body) -> collectConsts body constLst
    | LambdaOpt' (paramsArr, lastParam, body) -> collectConsts body constLst
    | Set' (expr1', expr2') -> collectConsts expr1' constLst @ collectConsts expr2' constLst
    | BoxSet' (var, expr') -> collectConsts expr' constLst
    | Const' (Sexpr (Vector v)) -> List.fold_right (fun sexpr lst -> collectConsts (Const' (Sexpr sexpr)) constLst @ lst) v constLst @ [(Sexpr (Vector v))]
    | Const' (Sexpr (Symbol v)) -> collectConsts (Const' (Sexpr (String v))) constLst @ [(Sexpr (Symbol v))] @ constLst
    | Const' x -> x :: constLst
    | _ -> constLst

  and makeSet lst =
    List.fold_right (fun const lst ->
        if List.mem const lst
        then lst
        else lst @ [const]) lst []

  and expandSet const accList =
    let rec expandPair = function
      | Pair (const', Nil) -> accList @ [Sexpr const'] @ [Sexpr (Pair (const', Nil))]
      | Pair (const', rest) -> accList @ [Sexpr const'] @ expandPair rest @ [Sexpr (Pair (const', rest))]
      | _ -> raise X_syntax_error in
    match const with
    | Sexpr (Pair (pair1, pair2)) -> expandPair (Pair (pair1, pair2))
    | Sexpr (Vector sexprs) -> (List.fold_right expandSet (List.map (fun sexpr -> Sexpr sexpr) sexprs) accList) @ [Sexpr (Vector sexprs)]
    | Sexpr sexpr -> accList @ [const]
    | Void -> accList @ [Void]

  and makeTable tempTable = List.fold_right (fun const accTable  ->  accTable @ [(const, makeOffset const  tempTable 0, makeStringTable const tempTable)]) (List.rev tempTable) []

  and makeOffset const constDataList offset =
    let head = List.hd constDataList in
    if const = head
    then offset
    else
      match head with
      | Void -> makeOffset const (List.tl constDataList) offset + sizeOfVoid
      | Sexpr Nil -> makeOffset const (List.tl constDataList) offset + sizeOfNil
      | Sexpr (Bool _) -> makeOffset const (List.tl constDataList) offset + sizeOfBool
      | Sexpr (Char _) -> makeOffset const (List.tl constDataList) offset + sizeOfChar
      | Sexpr (Number (Int _)) -> makeOffset const (List.tl constDataList) offset + sizeOfInt
      | Sexpr (Number (Float _)) -> makeOffset const (List.tl constDataList) offset + sizeOfFloat
      | Sexpr (Symbol _) -> makeOffset const (List.tl constDataList) offset + sizeOfSymbol
      | Sexpr (String st) -> makeOffset const (List.tl constDataList) offset + sizeOfLongSOB (String st)
      | Sexpr (Vector v) -> makeOffset const (List.tl constDataList) offset + sizeOfLongSOB (Vector v)
      | Sexpr (Pair _) -> makeOffset const (List.tl constDataList) offset + sizeOfPair

  and makeStringTable const tempTable =
    match const with
    | Void -> "\tMAKE_VOID"
    | Sexpr Nil -> "\tMAKE_NIL"
    | Sexpr (Bool false) -> "\tMAKE_BOOL(0)"
    | Sexpr (Bool true) -> "\tMAKE_BOOL(1)"
    | Sexpr (String x) -> "\tMAKE_LITERAL_STRING \"" ^ x ^ "\""
    | Sexpr (Number (Int x)) -> "\tMAKE_LITERAL_INT(" ^ string_of_int x ^ ")"
    | Sexpr (Number (Float x)) -> "\tMAKE_LITERAL_FLOAT(" ^ string_of_float x ^ ")"
    | Sexpr (Char x) -> "\tMAKE_LITERAL_CHAR(" ^ string_of_int (Char.code x) ^ ")"
    | Sexpr (Pair (x, y)) -> "\tMAKE_LITERAL_PAIR(const_tbl + " ^ string_of_int (makeOffset (Sexpr x) tempTable 0) ^ ", const_tbl + " ^ string_of_int (makeOffset (Sexpr y) tempTable 0) ^ ")"
    | Sexpr (Symbol x) -> "\tMAKE_LITERAL_SYMBOL(const_tbl + " ^ string_of_int (makeOffset (Sexpr (String x)) tempTable 0) ^")"
    | Sexpr (Vector v) -> "\tMAKE_LITERAL_VECTOR " ^ String.concat ", " (List.map (fun sexpr -> "const_tbl + " ^ string_of_int (makeOffset (Sexpr sexpr) tempTable 0)) v)

  let make_consts_tbl asts =
    makeTable (makeSet (List.rev ([Void; Sexpr Nil; Sexpr (Bool false); Sexpr( Bool true)] @ (List.fold_right expandSet (makeSet (List.fold_right (fun expr' accList -> accList @ collectConsts expr' []) asts [])) []))))
  (* makeTable (makeSet (List.rev ([Void; Sexpr Nil; Sexpr (Bool false); Sexpr( Bool true)] @ List.rev (List.fold_right expandSet (makeSet (collectConsts asts [])) []))));; *)

  let rec collectFreeVars expr' varList =
    match expr' with
    | Seq' bodies|Or' bodies ->
      List.fold_right (fun expr' lst -> lst @ collectFreeVars expr' varList) bodies varList
    | If' (test, dit, dif) ->
      collectFreeVars test varList @ collectFreeVars dit varList @ collectFreeVars dif varList
    | Def' (expr1', expr2') ->
      collectFreeVars expr1' varList @ collectFreeVars expr2' varList
    | Applic' (expr', expr'List)|ApplicTP' (expr', expr'List) ->
      collectFreeVars expr' varList @ List.fold_right (fun expr' lst -> lst @ collectFreeVars expr' varList) expr'List varList
    | LambdaSimple' (paramsArr, body) -> collectFreeVars body varList
    | LambdaOpt' (paramsArr, lastParam, body) -> collectFreeVars body varList
    | Set' (expr1', expr2') -> collectFreeVars expr1' varList @ collectFreeVars expr2' varList
    | Var' (VarFree st)|Box' (VarFree st)|BoxGet' (VarFree st) -> varList @ [st]
    | BoxSet' (VarFree st, expr') -> varList @ [st] @ collectFreeVars expr' varList
    | BoxSet' (_, expr') -> collectFreeVars expr' varList
    | _ -> varList

  let get_const_address c consts_tbl = 
    let const_row = List.find (fun (const, _, _) ->
        let matcher = (fun const c ->
            match const, c with
            | Void, Void -> true
            | Sexpr s1, Sexpr s2 -> sexpr_eq s1 s2
            | _ -> false) in
        matcher const c) consts_tbl in
    "const_tbl + " ^ string_of_int ((fun (_, offset, _) -> offset) const_row)

  let get_fvar_address const fvars_tbl =
    let fvar = List.find (fun (st, _) -> st = const) fvars_tbl in
    "fvar_tbl + WORD_SIZE * " ^ string_of_int ((fun (_, offset) -> offset) fvar)
  ;;

  (* Counters *)
  let counterGen =
    fun () ->
      let count = ref (-1) in
      fun (toIncr) ->
        if (toIncr)
        then
          (incr count;
           !count)
        else !count;;

  let orCounter =
    let count = counterGen () in
    fun toIncr ->
      ".exitOr" ^ string_of_int (count toIncr)

  and ifCounter =
    let count = counterGen () in
    fun toIncr isElse ->
      let numStr = string_of_int (count toIncr) in
      if isElse
      then ".else" ^ numStr
      else ".exitIf" ^ numStr

  and envTransLoopCounter =
    let count = counterGen () in
    fun toIncr ->
      ".transLoop" ^ string_of_int (count toIncr)

  and codeCounter =
    let count = counterGen () in
    fun toIncr isCode ->
      let count = string_of_int (count toIncr) in
      if isCode
      then ".code" ^ count
      else ".cont" ^ count

  and loopJmpCounter =
    let count = counterGen () in
    fun toIncr ->
      ".paramTransition" ^ string_of_int (count toIncr)

  and extendEnvCounter =
    let count = counterGen () in
    fun toIncr ->
      ".extendEnv" ^ string_of_int (count toIncr)

  and shiftCounter =
    let count = counterGen () in
    fun toIncr ->
      ".shiftFrame" ^ string_of_int (count toIncr)

  and enlargeCounter =
    let count = counterGen () in
    fun toIncr ->
      ".enlarge" ^ string_of_int (count toIncr)

  (* and  *)
  ;;

  let fvars_tbl = List.rev ["append"; "apply"; "<"; "="; ">"; "+"; "/"; "*"; "-"; "boolean?"; "car"; "cdr";
                            "char->integer"; "char?"; "cons"; "eq?"; "equal?"; "integer?"; "integer->char";
                            "length"; "list"; "list?"; "make-string"; "make-vector"; "map"; "not"; "null?";
                            "number?"; "pair?"; "procedure?"; "float?"; "set-car!"; "set-cdr!"; "string-length";
                            "string-ref"; "string-set!"; "string?"; "symbol?"; "symbol->string"; "vector";
                            "vector-length"; "vector-ref"; "vector-set!"; "vector?"; "zero?"]

  let make_fvars_tbl asts =
    let count = counterGen () in
    List.map (fun str -> str, count true) (makeSet (List.fold_right (fun ast acc -> acc @ collectFreeVars ast []) asts [] @ fvars_tbl));;

  let rec generate consts fvars lexDepth e =
    let rec generateArgs =
      function
      | [] -> ""
      | arg :: rest -> "
" ^ generate consts fvars lexDepth arg ^ "
\tpush rax" ^ generateArgs rest in
    match e with
    | Const' x -> "\tmov rax, " ^ get_const_address x consts ^ " ;GETING Const"
    | Var' (VarParam (_, minor)) -> "\tmov rax, PVAR(" ^ string_of_int minor ^ ") ;GETTING VarParam"
    | Set' (Var' (VarParam (_, minor)), expr') ->
      generate consts fvars lexDepth expr' ^ " ;SETTING VarParam
\tmov PVAR(" ^ string_of_int minor ^ "), rax
\tmov rax, SOB_VOID_ADDRESS"
    | Var' (VarBound (_, major, minor)) ->
      "\tmov rax, qword [rbp + 8 * 2] ;GETTING VarBound
\tmov rax, qword [rax + 8 * " ^ string_of_int major ^ "]
\tmov rax, qword [rax + 8 * " ^ string_of_int minor ^ "]"
    | Set' (Var' (VarBound (name, major, minor)), expr') ->
      generate consts fvars lexDepth expr' ^ " ;SETTING VarBound
" ^ generate consts fvars lexDepth (Var' (VarBound (name, major, minor))) ^ "
\tmov rax, SOB_VOID_ADDRESS"
    | Var' (VarFree v) -> "\tmov rax, qword [" ^ get_fvar_address v fvars ^ "] ;GETTING VarFree"
    | Set' (Var' (VarFree v), expr') ->
      generate consts fvars lexDepth expr' ^ " ;SETTING VarFree
\tmov qword [" ^ get_fvar_address v fvars ^ "], rax
\tmov rax, SOB_VOID_ADDRESS"
    | Seq' lst -> String.concat "\n" (List.map (generate consts fvars lexDepth) lst)
    | Or' lst ->
      let lable = orCounter true
      and lastExpr = List.hd (List.rev lst)
      and newlst = List.rev (List.tl (List.rev lst)) in
      let txt = "
\tcmp rax, SOB_FALSE_ADDRESS
\tjne " ^ lable ^ "\n" in
      String.concat txt (List.map (generate consts fvars lexDepth) newlst) ^ txt ^
      generate consts fvars lexDepth lastExpr ^ "\n" ^
      lable ^":"
    | If' (test, dit, dif) ->
      let lableElse = ifCounter true true
      and lableExit = ifCounter false false in
      generate consts fvars lexDepth test ^ "
\tcmp rax, SOB_FALSE_ADDRESS
\tje " ^ lableElse ^ "\n" ^
      generate consts fvars lexDepth dit ^ "\n\tjmp " ^ lableExit ^ "\n" ^
      lableElse ^ ":\n" ^
      generate consts fvars lexDepth dif ^ "\n" ^
      lableExit ^ ":"
    | Box' (VarParam (name, minor)) ->"\t;BOXING\n" ^
                                      generate consts fvars lexDepth (Var' (VarParam (name, minor))) ^ "
\tmov rbx, WORD_SIZE
\tMALLOC rbx, rbx
\tmov qword [rbx], rax
\tmov rax, rbx"
    | BoxGet' v -> "\t;BoxGet\n"^
                   generate consts fvars lexDepth (Var' v) ^ "
\tmov rax, qword [rax]"
    | BoxSet' (v, expr') -> "\t;BoxSet\n" ^
                            generate consts fvars lexDepth expr' ^ "
\tpush rax\n" ^
                            generate consts fvars lexDepth (Var' v) ^ "
\tpop qword [rax]
\tmov rax, const_tbl + 0"
    | Def' (Var' (VarFree v), expr') -> generate consts fvars lexDepth (Set' (Var' (VarFree v), expr'))
    | LambdaSimple' (paramlst, body) ->
      let paramTransition = loopJmpCounter true
      and extendEnv = extendEnvCounter true in
      let envCreation = "\tmov rbx, " ^ string_of_int (lexDepth + 1) ^ "
\tshl rbx, 3
\tMALLOC rbx, rbx
" ^ "
\tmov rdx, " ^ (string_of_int (lexDepth)) ^ "               ;rdx = |env|
\tmov r8, 0               ;index1 = 0
\tmov r9, 1               ;index2 = 1" ^ "
" ^ (extendEnv) ^ ":
\tcmp r8, rdx          ;if(index == |env|)
\tje " ^ (extendEnv) ^ "End    ;jump to end
\tmov r12, qword[rbp + 8 * 2]  ;r12 = env
\tmov r13, WORD_SIZE
\timul r13, r8
\tadd r12, r13             ;r12 = env[i]
\tmov r13, rbx             ;r13 = Extenv[0]
\tmov r14, WORD_SIZE
\timul r14, r9
\tadd r13, r14             ;r13 = Extenv[j]
\tmov r10, qword[r12]      ;r10 = [env[i]]
\tmov qword[r13], r10      ;[r13] = Extenv[j] = [env[i]]
\tinc r8                  ;index1++
\tinc r9                  ;index2++
\tjmp " ^ (extendEnv) ^ "
" ^ (extendEnv) ^ "End:
\tmov r8, qword [rbp + 3 * 8] ;r8 holds the params counter
\tshl r8, 3
\tMALLOC r8, r8
\tmov	rcx, qword [rbp + 3 * 8]
\tmov r10, 0   ;r10 = i = 0
\t" ^ paramTransition ^ ":
\tcmp r10, rcx
\tje " ^ paramTransition ^ "End
\t\tmov r9, PVAR(r10)
\t\tmov r13, r8  ;r13 = ExtEnv[0]
\t\tmov r14, WORD_SIZE
\t\timul r14, r10 
\t\tadd r13, r14  ;r13 = ExtEnv[i]
\t\tmov [r13], r9
\t\tinc r10
\tjmp " ^ paramTransition ^ "
" ^ paramTransition ^ "End:"
      and closureCreation =
        let countCode = codeCounter true true
        and countCont = codeCounter false false in "
" ^ "\tmov qword[rbx], r8 ;ExtEnv[0] = vector
\tmov rax, rbx
\tMAKE_CLOSURE(rax, rbx, " ^ countCode ^ ") ;rbx = ExtEnv, countCode = code = LCode
\tjmp " ^ countCont ^ "
" ^ countCode ^ ": ;Generate the body
\tenter 0, 0
" ^ generate consts fvars (lexDepth + 1) body ^ "
\tleave
\tret
" ^ countCont ^ ":" in 
      envCreation ^ closureCreation
    | LambdaOpt'(paramList, lastParam, body) ->
      let paramTransition = loopJmpCounter true
      and extendEnv = extendEnvCounter true in
      let envCreation = "\tmov rbx, " ^ string_of_int (lexDepth + 1) ^ "
\tshl rbx, 3
\tMALLOC rbx, rbx
" ^ "
\tmov rdx, " ^ (string_of_int (lexDepth)) ^ "               ;rdx = |env|
\tmov r8, 0               ;index1 = 0
\tmov r9, 1               ;index2 = 1" ^ "
" ^ (extendEnv) ^ "Opt:
\tcmp r8, rdx          ;if(index == |env|)
\tje " ^ (extendEnv) ^ "OptEnd    ;jump to end
\tmov r12, qword[rbp + 8 * 2]  ;r12 = env
\tmov r13, WORD_SIZE
\timul r13, r8
\tadd r12, r13             ;r12 = env[i]
\tmov r13, rbx             ;r13 = Extenv[0]
\tmov r14, WORD_SIZE
\timul r14, r9
\tadd r13, r14             ;r13 = Extenv[j]
\tmov r10, qword[r12]      ;r10 = [env[i]]
\tmov qword[r13], r10      ;[r13] = Extenv[j] = [env[i]]
\tinc r8                  ;index1++
\tinc r9                  ;index2++
\tjmp " ^ (extendEnv) ^ "Opt
" ^ (extendEnv) ^ "OptEnd:
\tmov r8, qword [rbp + 3 * 8] ;r8 holds the params counter
\tshl r8, 3
\tMALLOC r8, r8
\tmov	rcx, qword [rbp + 3 * 8]
\tmov r10, 0   ;r10 = i = 0
\t" ^ paramTransition ^ "Opt:
\tcmp r10, rcx
\tje " ^ paramTransition ^ "OptEnd
\t\tmov r9, PVAR(r10)
\t\tmov r13, r8  ;r13 = ExtEnv[0]
\t\tmov r14, WORD_SIZE
\t\timul r14, r10 
\t\tadd r13, r14  ;r13 = ExtEnv[i]
\t\tmov [r13], r9
\t\tinc r10
\tjmp " ^ paramTransition ^ "Opt
" ^ paramTransition ^ "OptEnd:"
      and closureCreation =
        let countCode = codeCounter true true
        and countCont = codeCounter false false
        and enlargeCount = enlargeCounter true in "
" ^ "\tmov qword[rbx], r8 ;ExtEnv[0] = vector
\tmov rax, rbx
\tMAKE_CLOSURE(rax, rbx, " ^ countCode ^ "Opt) ;rbx = ExtEnv, countCode = code = LCode
\tjmp " ^ countCont ^ "Opt

" ^ countCode ^ "Opt: ;Generate the body
;Adjust the stack for the
;optional arguments
\tmov rcx, [rsp+8*2]               ;rcx=# of applic args
\tmov r14, " ^ string_of_int (List.length paramList) ^ "         ;r14=# of lambda args (without the last one)
\tcmp rcx, r14
\tje " ^ enlargeCount ^ "
\tsub rcx, r14       ;rcx = rcx-r14
\tdec rcx            ;rcx = times loop
\tmov r11, rbp
\tsub r11, WORD_SIZE * 2        ;r11=last applic arg (need to be 8 not 16)
\tmov r8, [r11]
\tMAKE_PAIR(r13, r8, SOB_NIL_ADDRESS)
" ^ enlargeCount ^ "Loop:
\t\tsub r11, WORD_SIZE
\t\tmov r12, r13
\tmov r8, [r11]
\t\tMAKE_PAIR(r13, r8, r12)
\tloop " ^ enlargeCount ^ "Loop
\tmov [r11], r13
\tjmp "^ enlargeCount ^ "Exit
" ^ enlargeCount ^ ":
\tadd rcx, 3
\tmov r15, rsp
" ^ enlargeCount ^ "Loop1:
\t\tmov r14, [r15]
\t\tmov [r15 - WORD_SIZE], r14
\t\tadd r15, WORD_SIZE
\tloop " ^ enlargeCount ^ "Loop1
\tmov qword [r15 - WORD_SIZE], SOB_NIL_ADDRESS
\tsub rsp, WORD_SIZE
\tinc qword [rsp + 2 * WORD_SIZE]
" ^ enlargeCount ^ "Exit:
\tpush rbp
\tmov rbp, rsp
" ^ generate consts fvars (lexDepth + 1) body ^ "
\tleave
\tret
" ^ countCont ^ "Opt:" in 
      envCreation ^ closureCreation
    | Applic' (proc, argList) ->
      generateArgs (List.rev argList) ^ "
\tpush " ^ string_of_int (List.length argList) ^ "
" ^ generate consts fvars lexDepth proc ^ "
\tCLOSURE_ENV rbx, rax
\tpush rbx
\tCLOSURE_CODE rbx, rax
\tcall rbx
\tadd rsp, WORD_SIZE * 1     ; pop env
\tpop rbx           ; pop arg count
\tshl rbx, 3       ; rbx = rbx * 8
\tadd rsp, rbx     ; pop args"
    | ApplicTP' (proc, argList) ->
      (* let shiftCount = shiftCounter true in *)
      generateArgs (List.rev argList) ^ "
\tpush " ^ string_of_int (List.length argList) ^ "
 " ^ generate consts fvars lexDepth proc ^ "
\tCLOSURE_ENV rbx, rax
\tpush rbx
\tCLOSURE_CODE rbx, rax
\tpush qword [rbp + WORD_SIZE] ;ret address
\tmov r15, qword[rbp]
\tSHIFT_FRAME " ^ string_of_int (4 + List.length argList) ^ "
\tadd rsp, 40
\tmov rbp, r15
\tjmp rbx"
    | _ ->""
end;;

let string_to_asts s = List.map Semantics.run_semantics (Tag_Parser.tag_parse_expressions (Reader.read_sexprs s));;

let asts = string_to_asts
    "\'a";;
let consts_tbl = Code_Gen.make_consts_tbl asts
and fvars_tbl = Code_Gen.make_fvars_tbl asts;;
(* let generate = Code_Gen.generate consts_tbl fvars_tbl 0;;
let code_fragment = String.concat "\n\n"
    (List.map
       (fun ast -> (generate ast) ^ "\n\tcall write_sob_if_not_void")
       asts);; *)