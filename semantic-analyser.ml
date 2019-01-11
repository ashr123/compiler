(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
*)

#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const' (Sexpr s1), Const' (Sexpr s2) -> sexpr_eq s1 s2
  | Var' (VarFree v1), Var' (VarFree v2) -> String.equal v1 v2
  | Var' (VarParam (v1, mn1)), Var' (VarParam (v2, mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var' (VarBound (v1, mj1, mn1)), Var' (VarBound (v2, mj2, mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If' (t1, th1, el1), If' (t2, th2, el2) -> (expr'_eq t1 t2) &&
                                              (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'  l1, Seq' l2
    | Or' l1, Or' l2) -> List.for_all2 expr'_eq l1 l2
  | (Set' (var1, val1), Set' (var2, val2)
    | Def' (var1, val1), Def' (var2, val2)) -> (expr'_eq var1 var2) &&
                                               (expr'_eq val1 val2)
  | LambdaSimple' (vars1, body1), LambdaSimple' (vars2, body2) ->
    (List.for_all2 String.equal vars1 vars2) &&
    (expr'_eq body1 body2)
  | LambdaOpt' (vars1, var1, body1), LambdaOpt' (vars2, var2, body2) ->
    (String.equal var1 var2) &&
    (List.for_all2 String.equal vars1 vars2) &&
    (expr'_eq body1 body2)
  | Applic' (e1, args1), Applic' (e2, args2)
  | ApplicTP' (e1, args1), ApplicTP' (e2, args2) ->
    (expr'_eq e1 e2) &&
    (List.for_all2 expr'_eq args1 args2)
  | Box' _, Box' _ -> true
  | BoxGet' _, BoxGet' _ -> true
  | BoxSet' (_, v1), BoxSet' (_, v2) -> expr'_eq v1 v2 
  | _ -> false;;


(* exception X_syntax_error;; *)

(* module type SEMANTICS = sig
   val run_semantics : expr -> expr'
   val annotate_lexical_addresses : expr -> expr'
   val annotate_tail_calls : expr' -> expr'
   val box_set : expr' -> expr'
   end;; *)

module Semantics : sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end = struct

  let rec parseExpr expr varArr =
    match expr with
    | LambdaSimple (paramsArr, body) ->
      LambdaSimple' (paramsArr, parseExpr body (List.rev ((List.rev varArr) @ [paramsArr])))
    | LambdaOpt (paramsArr, lastParm, body) ->
      LambdaOpt' (paramsArr, lastParm, (parseExpr body (List.rev ((List.rev varArr) @ [paramsArr @ [lastParm]]))))
    | Applic (expr, exprList) ->
      Applic' (parseExpr expr varArr, List.map (fun expr -> parseExpr expr varArr) exprList)
    | Seq exprList -> Seq' (List.map (fun expr -> parseExpr expr varArr) exprList)
    | If (test, dit, dif) -> If' (parseExpr test varArr, parseExpr dit varArr, parseExpr dif varArr)
    | Def (expr1, expr2) -> Def' (parseExpr expr1 varArr, parseExpr expr2 varArr)
    | Or exprList -> Or' (List.map (fun expr -> parseExpr expr varArr) exprList)
    | Set (expr1, expr2) -> Set' (parseExpr expr1 varArr, parseExpr expr2 varArr)
    | Var str -> searchAndTagVarInArr str varArr 0
    | Const _x -> Const' _x

  and searchAndTagVarInArr var lst majorIndex =
    match lst with
    | [] -> Var' (VarFree var)
    | h :: t ->
      let minorIndex = find var h 0 in
      if minorIndex > -1
      then if majorIndex = 0
        then Var' (VarParam (var, minorIndex))
        else Var' (VarBound (var, majorIndex - 1, minorIndex))
      else searchAndTagVarInArr var t (majorIndex + 1)

  and find x lst index =
    match lst with
    | [] -> -1
    | h :: t ->
      if x = h
      then index
      else find x t (index + 1)

  and parseTP (expr': expr') inTP =
    match expr' with
    | LambdaSimple' (paramsArr, body) -> LambdaSimple' (paramsArr, parseTP body true)
    | LambdaOpt' (paramsArr, lastParm, body) -> LambdaOpt' (paramsArr, lastParm, parseTP body true)
    | If' (test, dit, dif) -> If' (parseTP test false, parseTP dit inTP, parseTP dif inTP)
    | Seq' bodies ->
      let lastBody = List.hd (List.rev bodies)
      and lstWithoutLastBody = List.rev (List.tl (List.rev bodies)) in
      Seq' ((List.map (fun body -> parseTP body false) lstWithoutLastBody) @ [parseTP lastBody inTP])
    | Or' bodies ->
      let lastBody = List.hd (List.rev bodies)
      and lstWithoutLastBody = List.rev (List.tl (List.rev bodies)) in
      Or' ((List.map (fun body -> parseTP body false) lstWithoutLastBody) @ [parseTP lastBody inTP]) 
    | Set' (expr1', expr2') -> Set' (parseTP expr1' false, parseTP expr2' false)
    | Def' (expr1', expr2') -> Def' (parseTP expr1' false, parseTP expr2' inTP)
    | Applic' (expr', expr'List) ->
      if inTP
      then ApplicTP' (parseTP expr' false, List.map (fun expr' -> parseTP expr' false) expr'List) (** change back to ApplicTP' *)
      else Applic' (parseTP expr' false, List.map (fun expr' -> parseTP expr' false) expr'List)
    | _x -> _x (* for vars' and consts' *)

  and counterGen =
    fun () ->
      let count = ref (-1) in
      fun (toIncr) ->
        if (toIncr)
        then
          (incr count;
           !count)
        else
          !count

  and print_list =
    function
    | [] -> print_string "]\n"; ()
    | e :: [] -> print_int e; print_list []
    | e :: l -> print_int e; print_string "; "; print_list l

  and print_boolean =
    function
    | true -> print_string " true\n"; ()
    | false -> print_string " false\n"; ()

  and print_int_int_list =
    function
    | [] -> print_string "]\n"; ()
    | (e1, e2) :: [] -> print_char '('; print_int e1; print_string ", "; print_int e2; print_char ')'; print_list []
    | (e1, e2) :: li -> print_char '('; print_int e1; print_string ", "; print_int e2; print_char ')'; print_string "; "; print_int_int_list li

  and removeShadow body param paramsAcc =
    match body with
    | LambdaSimple' (paramsArr, body) -> LambdaSimple' (paramsArr, removeShadow body param (paramsAcc @ paramsArr))
    | LambdaOpt' (paramsArr, lastParm, body) -> LambdaOpt' (paramsArr, lastParm, removeShadow body param (paramsAcc @ (paramsArr @ [lastParm])))
    | If' (test, dit, dif) -> If' (removeShadow test param paramsAcc, removeShadow dit param paramsAcc, removeShadow dif param paramsAcc)
    | Seq' bodies ->
      Seq' (List.map (fun body -> removeShadow body param paramsAcc) bodies)
    | Or' bodies ->
      Or' (List.map (fun body -> removeShadow body param paramsAcc) bodies)
    | Set' (expr1', expr2') ->
      Set' ((match expr1' with
          | Var' (VarParam (name, minorIndex)) ->
            if List.mem param paramsAcc && name = param
            then Var' (VarParam (name ^ "$", minorIndex))
            else Var' (VarParam (name, minorIndex))
          | Var' (VarBound (name, majorIndex, minorIndex)) ->
            if List.mem param paramsAcc && name = param
            then Var' (VarBound (name ^ "$", majorIndex, minorIndex))
            else Var' (VarBound (name, majorIndex, minorIndex))
          | Var' (VarFree x)-> Var' (VarFree x)
          | _ -> raise X_syntax_error), removeShadow expr2' param paramsAcc) 
    | Def' (expr1', expr2') -> Def' (removeShadow expr1' param paramsAcc, removeShadow expr2' param paramsAcc)
    | Applic' (expr', expr'List) ->
      Applic' (removeShadow expr' param paramsAcc, List.map (fun expr' -> removeShadow expr' param paramsAcc) expr'List)
    | ApplicTP' (expr', expr'List) ->
      ApplicTP' (removeShadow expr' param paramsAcc, List.map (fun expr' -> removeShadow expr' param paramsAcc) expr'List)
    | Var' (VarParam (name, minorIndex)) ->
      if List.mem param paramsAcc && name = param
      then Var' (VarParam (name ^ "$", minorIndex))
      else Var' (VarParam (name, minorIndex))
    | Var' (VarBound (name, majorIndex, minorIndex)) ->
      if List.mem param paramsAcc && name = param
      then Var' (VarBound (name ^ "$", majorIndex, minorIndex))
      else Var' (VarBound (name, majorIndex, minorIndex))
    | _x -> _x (* for consts' *)

  and isNeedToBeBoxed (param: string) (body: expr'): bool =
    let cartesian l l' = List.concat (List.map (fun e -> List.map (fun e' -> (e, e')) l') l)
    and newBody = removeShadow body param [] in
    let readList = checkRead (counterGen ()) param newBody
    and writeList = checkWrite (counterGen ()) param newBody in
    (* print_string "read list: ["; print_list readList;
       print_string "write list: ["; print_list writeList;  *)
    let joinedList = cartesian readList writeList in
    (* print_string "joined list: ["; print_int_int_list joinedList; *)
    let res = List.fold_right (fun (readNum, writeNum) res -> res || (readNum <> writeNum)) joinedList false in
    (* print_string param; print_boolean res; *)
    res

  and checkRead count param (body: expr') =
    match body with
    | LambdaSimple' (_, body)|LambdaOpt' (_, _, body) -> 
      let c = count true in
      if checkRead count param body <> []
      then [c]
      else []
    | Applic' (expr', expr'List)|ApplicTP' (expr', expr'List) ->
      checkRead count param expr' @ List.fold_right (fun expr' lst -> lst @ checkRead count param expr') expr'List []
    | Seq' expr'List -> List.fold_right (fun expr' lst -> lst @ checkRead count param expr') expr'List []
    | If' (test, dit, dif) -> checkRead count param test @ checkRead count param dit @ checkRead count param dif
    | Def' (expr1', expr2') -> checkRead count param expr1' @ checkRead count param expr2'
    | Or' expr'List -> List.fold_right (fun expr' lst -> lst @ checkRead count param expr') expr'List []
    | Set' (expr1', expr2') -> checkRead count param expr2'
    | Var' str ->
      (match str with
       | VarParam (x, _)|VarBound (x, _, _) ->
         if x = param
         then [-2]
         else []
       | VarFree _ -> [])
    | Const' _ -> []
    | _ -> raise X_syntax_error

  and checkWrite count param body =
    match body with
    | LambdaSimple' (_, body)|LambdaOpt' (_, _, body) -> 
      let c = count true in 
      if checkWrite count param body <> []
      then [c]
      else []
    | Applic' (expr', expr'List)|ApplicTP' (expr', expr'List) ->
      checkWrite count param expr' @ List.fold_right (fun expr' lst -> lst @ checkWrite count param expr') expr'List []
    | Seq' expr'List -> List.fold_right (fun expr' lst -> lst @ checkWrite count param expr') expr'List []
    | If' (test, dit, dif) -> checkWrite count param test @ checkWrite count param dit @ checkWrite count param dif
    | Def' (expr1', expr2') -> checkWrite count param expr1' @ checkWrite count param expr2'
    | Or' expr'List -> List.fold_right (fun expr' lst -> lst @ checkWrite count param expr') expr'List []
    | Set' (expr1', expr2') ->
      (match expr1' with
       (* print_string "param: "; print_string param; print_string ", majorIndex: "; print_int majorIndex; print_string ", count: "; print_int (count false); print_newline (); *)
       | Var' (VarParam (x, _))|Var' (VarBound (x, _, _)) ->
         if x = param
         then [-2]
         else []
       | Var' (VarFree _)-> []
       | _ -> raise X_syntax_error) @ checkWrite count param expr2'
    | Var' _ -> []
    | Const' _ -> []
    | _ -> raise X_syntax_error

  and updateParamList paramList = List.map (fun (varName, majorIndex) -> (varName, majorIndex + 1)) paramList

  and addBoxParam paramList paramsArr body = List.fold_right (fun p lst ->
      (* print_string "BOOL: "; print_boolean (isNeedToBeBoxed param body); print_char '\n'; *)
      if isNeedToBeBoxed p body
      then  lst @ [(p, -1)]
      else lst) paramsArr paramList

  and  print_pair_list = function
    | [] -> print_string "]\n"; ()
    | (name, majorIndex) :: [] -> print_string "(\""; print_string name; print_string "\", "; print_int majorIndex; print_string ")"; print_pair_list []
    | (name, majorIndex) :: li -> print_string "(\""; print_string name; print_string "\", "; print_int majorIndex; print_string "); "; print_pair_list li

  and parseBoxing expr' paramsList =
    let makeSeq' boxParam paramsArr body =
      Seq' ((List.fold_right (fun (name, majorIndex) acc ->
          if majorIndex = -1
          then let minor = find name paramsArr 0 in
            (* print_string "paramsList :["; print_pair_list paramsArr; *)
            acc @ [Set' (Var' (VarParam (name, minor)), Box' (VarParam (name, minor)))]
          else acc) boxParam []) @ [body]) in
    match expr' with
    | Seq' bodies -> Seq' (List.map (fun expr' -> parseBoxing expr' paramsList) bodies)
    | Or' bodies -> Or' (List.map (fun expr' -> parseBoxing expr' paramsList) bodies)
    | If' (test, dit, dif) ->
      If' (parseBoxing test paramsList, parseBoxing dit paramsList, parseBoxing dif paramsList)
    | Def' (expr1', expr2') ->
      Def' (parseBoxing expr1' paramsList, parseBoxing expr2' paramsList)
    | Applic' (expr', expr'List) ->
      Applic' (parseBoxing expr' paramsList, List.map (fun expr' -> parseBoxing expr' paramsList) expr'List)
    | ApplicTP' (expr', expr'List) ->
      ApplicTP' (parseBoxing expr' paramsList, List.map (fun expr' -> parseBoxing expr' paramsList) expr'List)      
    | LambdaSimple' (paramsArr, body) ->
      let boxParam = addBoxParam (updateParamList paramsList) paramsArr body in
      (* print_string "box param: ["; print_pair_list boxParam; *)
      if List.exists (fun (_, index) -> index = -1) boxParam
      then LambdaSimple' (paramsArr, makeSeq' boxParam paramsArr (parseBoxing body boxParam))
      else LambdaSimple' (paramsArr, parseBoxing body boxParam)
    | LambdaOpt' (paramsArr, lastParam, body) ->
      let joinedList = (paramsArr @ [lastParam]) in
      let boxParam = addBoxParam (updateParamList paramsList) joinedList body in
      if List.exists (fun (_, index) -> index = -1) boxParam
      then LambdaOpt' (paramsArr, lastParam, makeSeq' boxParam joinedList (parseBoxing body boxParam))
      else LambdaOpt' (paramsArr, lastParam, parseBoxing body boxParam)
    | Set' (Var' x, expr2') -> 
      (match x with
       | VarParam (name, minorIndex) ->
         if List.mem (name, -1) paramsList
         then BoxSet' (VarParam (name, minorIndex), parseBoxing expr2' paramsList)
         else Set' (Var' x, parseBoxing expr2' paramsList)
       | VarBound (name, majorIndex, minorIndex) ->
         if List.mem (name, majorIndex) paramsList
         then BoxSet' (VarBound (name, majorIndex, minorIndex), parseBoxing expr2' paramsList)
         else Set' (Var' x, parseBoxing expr2' paramsList)
       | _ -> Set' (Var' x, parseBoxing expr2' paramsList))
    | Var' (VarParam (name, minorIndex)) ->
      if List.mem (name, -1) paramsList
      then BoxGet' (VarParam (name, minorIndex))
      else Var' (VarParam (name, minorIndex))
    | Var' (VarBound (name, majorIndex, minorIndex)) ->
      if List.mem (name, majorIndex ) paramsList
      then BoxGet' (VarBound (name, majorIndex, minorIndex))
      else Var' (VarBound (name, majorIndex, minorIndex))
    | _x -> _x (* for consts' *)

  and annotate_lexical_addresses e = parseExpr e []

  and annotate_tail_calls e = parseTP e false

  and box_set e = parseBoxing e []

  and run_semantics expr = box_set (annotate_tail_calls (annotate_lexical_addresses expr));;

end (* struct Semantics *)