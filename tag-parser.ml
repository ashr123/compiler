(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
*)

#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const (Sexpr s1), Const (Sexpr s2) -> sexpr_eq s1 s2
  | Var v1, Var v2 -> String.equal v1 v2
  | If (t1, th1, el1), If (t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                            (expr_eq el1 el2)
  | (Seq l1, Seq l2
    | Or l1, Or l2) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set (var2, val2)
    | Def (var1, val1), Def (var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple (vars1, body1), LambdaSimple (vars2, body2) ->
    (List.for_all2 String.equal vars1 vars2) &&
    (expr_eq body1 body2)
  | LambdaOpt (vars1, var1, body1), LambdaOpt (vars2, var2, body2) ->
    (String.equal var1 var2) &&
    (List.for_all2 String.equal vars1 vars2) &&
    (expr_eq body1 body2)
  | Applic (e1, args1), Applic (e2, args2) ->
    (expr_eq e1 e2) &&
    (List.for_all2 expr_eq args1 args2)
  | _ -> false;;


exception X_syntax_error;;

(* module type TAG_PARSER = sig
   val tag_parse_expression : sexpr -> expr
   val tag_parse_expressions : sexpr list -> expr list
   end;; (*signature TAG_PARSER *)*)

module Tag_Parser: sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end = struct

  let reserved_word_list =
    ["and"; "begin"; "cond"; "define"; "else";
     "if"; "lambda"; "let"; "let*"; "letrec"; "or";
     "quasiquote"; "quote"; "set!"; "unquote";
     "unquote-splicing"];;

  (* work on the tag parser starts here *)

  let varParser str = List.mem str reserved_word_list (* ormap (fun reservedStr -> String.equal str reservedStr) reserved_word_list;; *)

  let rec tag_parse_expression sexpr =
    match sexpr with
    | Pair (Symbol "cond", cond) -> parseCond cond
    | Pair (Symbol "letrec", Pair (args, bodies)) -> parseLetRec args bodies
    | Pair (Symbol "let", Pair (args, bodies)) ->
      tag_parse_expression (Pair (Pair (Symbol "lambda", Pair (argsToVarSymbol args, bodies)), argsToVarValue args))
    | Pair (Symbol "let*", Pair (args, bodies)) -> parseLetStar args bodies
    | Pair (Symbol "begin", bodies) -> sequencesExpr bodies
    | Pair (Symbol "define", Pair (Pair (Symbol varName, args), bodies)) ->
      tag_parse_expression (Pair (Symbol "define", Pair (Symbol varName, Pair (Pair (Symbol "lambda", Pair (args, bodies)), Nil))))
    | Pair (Symbol "define", Pair (Symbol(varRef), Pair (varVal , Nil))) ->
      Def (tag_parse_expression (Symbol varRef), tag_parse_expression varVal)
    | Pair (Symbol "set!", Pair (Symbol sym, Pair (arg, Nil))) ->
      Set (tag_parse_expression (Symbol sym), tag_parse_expression arg)
    | Pair (Symbol "lambda", Pair (args, bodies)) -> parseLambda args bodies
    | Pair (Symbol "if", Pair (test, Pair (dit, Nil))) ->
      If (tag_parse_expression test, tag_parse_expression dit, Const Void)
    | Pair (Symbol "if", Pair (test, Pair (dit, Pair (dif, Nil)))) ->
      If (tag_parse_expression test, tag_parse_expression dit, tag_parse_expression dif)
    | Pair (Symbol "and", args) -> parseAnd args
    | Pair (Symbol "or", args) -> parseOr args
    | Pair ( Symbol "quasiquote", Pair (x, Nil)) -> parseQuasiquote x
    | Pair (Symbol "quote", Pair (x, Nil)) -> Const (Sexpr x)
    | Pair (Symbol "unquote", Pair (x, Nil)) -> raise X_syntax_error
    | Pair (funcSexpr, args) ->
      Applic (tag_parse_expression funcSexpr, tag_parse_expressions (pairToList args))
    | Number _|Bool _|String _|Char _|Vector _|Nil -> Const (Sexpr sexpr)
    | Symbol x ->
      if not (varParser x)
      then Var x
      else raise X_syntax_error

  and parseQuasiquote x =
    match x with
    | Number _|Bool _|String _|Char _ -> tag_parse_expression x
    | Nil -> tag_parse_expression (Pair (Symbol "quote", Pair (x, Nil)))
    | Symbol _ -> tag_parse_expression (Pair (Symbol "quote", Pair (x, Nil)))
    | Pair (Symbol "unquote", Pair (exp, Nil)) -> tag_parse_expression exp
    | Pair (Symbol "unquote-splicing", Pair (_, Nil)) -> raise X_syntax_error
    | Pair (Pair (Symbol "unquote-splicing", Pair (exp, Nil)), Nil) ->
      Applic (Var "append", [tag_parse_expression exp; Const (Sexpr Nil)])
    | Pair (Pair (Symbol "unquote-splicing", Pair (exp_a, Nil)), exp_b) ->
      Applic (Var "append", [tag_parse_expression exp_a; tag_parse_expression (Pair (Symbol "quasiquote", Pair (exp_b, Nil)))])
    | Pair (exp_a, Pair (Symbol "unquote-splicing", Pair (exp_b, Nil))) ->
      Applic (Var "cons", [tag_parse_expression (Pair (Symbol "quasiquote", Pair (exp_a, Nil))); tag_parse_expression exp_b])
    | Pair (exp_a, exp_b) ->
      Applic (Var "cons", [tag_parse_expression (Pair (Symbol "quasiquote", Pair (exp_a, Nil))); tag_parse_expression (Pair (Symbol "quasiquote", Pair (exp_b, Nil)))])
    | Vector list ->
      let expList = List.map (fun x -> tag_parse_expression (Pair (Symbol "quote", Pair (x, Nil)))) list in 
      Applic (Var "vector", expList)

  and parseCond cond =
    match cond with
    | Pair (Pair (Symbol "else", then1), _) -> tag_parse_expression (Pair (Symbol "begin", then1))
    | Pair (Pair (cond1, then1), Nil) -> tag_parse_expression (Pair (Symbol "if" ,Pair (cond1, Pair (Pair (Symbol "begin", then1), Nil))))
    | Pair (Pair (cond1, then1), nextCond) -> 
      tag_parse_expression (Pair (Symbol "if", Pair (cond1, Pair (Pair (Symbol "begin", then1), Pair (Pair (Symbol "cond", nextCond), Nil)))))
    | _ -> raise X_syntax_error

  and parseLetStar args bodies =
    match args with
    | Nil -> tag_parse_expression (Pair (Symbol "let", Pair (Nil, bodies)))
    | Pair (Pair (Symbol varName , Pair (varValue, Nil)), Nil) ->
      tag_parse_expression (Pair (Symbol "let", Pair (Pair (Pair (Symbol varName, Pair (varValue, Nil)), Nil), bodies)))
    | Pair (Pair (Symbol varName , Pair (varValue, Nil)), nextArgs) ->
      tag_parse_expression (Pair (Symbol "let", Pair (Pair (Pair (Symbol varName, Pair (varValue, Nil)), Nil), Pair (Pair (Symbol "let*", Pair (nextArgs, bodies)), Nil))))
    | _-> raise X_syntax_error

  and setBangArgs args =
    match args with
    | Pair (var, bodies) ->
      (match var with
       | Nil -> bodies
       | Pair (Pair (Symbol varName, Pair (varVal, _)), nextVar) ->
         Pair (Pair (Symbol "set!", Pair (Symbol varName, Pair (varVal, Nil))), setBangArgs (Pair (nextVar, bodies)))
       | _ -> raise X_syntax_error)
    | _ -> raise X_syntax_error

  and whateverLetRecVars x =
    match x with
    | Nil -> Nil
    | Pair (Pair (Symbol varName, varValue), nextVar) ->
      Pair (Pair (Symbol varName, Pair (Pair (Symbol "quote", Pair (Symbol "whatever", Nil)), Nil)), whateverLetRecVars nextVar)
    | _ -> raise X_syntax_error

  and parseLetRec args bodies =
    match args with
    | Nil -> tag_parse_expression (Pair (Symbol "let", Pair (Nil, bodies)))
    | _ -> tag_parse_expression (Pair (Symbol "let", Pair (whateverLetRecVars args, setBangArgs (Pair (args, bodies)))))

  and sequencesImplicitExpr bodies =
    match bodies with
    | Nil -> []
    | Pair (hd, Pair (tl, Nil)) -> [tag_parse_expression hd; tag_parse_expression tl]
    | Pair (hd, tail) -> List.append [tag_parse_expression hd] (sequencesImplicitExpr tail)
    | _-> raise X_syntax_error

  and sequencesExpr bodies =
    match bodies with
    | Nil -> Const Void
    | Pair (body, Nil) -> tag_parse_expression body
    | _ -> Seq (sequencesImplicitExpr bodies)

  and argsToVarSymbol args =
    match args with
    | Nil -> Nil
    | Pair (Pair (Symbol varName, Pair (_, Nil)), Nil) -> Pair (Symbol varName, Nil)
    | Pair (Pair (Symbol varName, Pair (_, Nil)), varNext) -> Pair (Symbol varName, argsToVarSymbol varNext)
    | _ -> raise X_syntax_error

  and argsToVarValue args =
    match args with
    | Nil -> Nil
    | Pair (Pair (Symbol _, Pair (varValue, Nil)), Nil) -> Pair (varValue, Nil)
    | Pair (Pair (Symbol _, Pair (varValue, Nil)), varNext) -> Pair (varValue, argsToVarValue varNext)
    | _ -> raise X_syntax_error

  and ifSimpleLambda args =
    match args with
    | Nil -> true
    | Pair (Symbol _, Symbol _) -> false
    | Pair (Symbol _, x) -> ifSimpleLambda x
    | Symbol x -> false
    | _ -> raise X_syntax_error

  and parseLambda args bodies =
    if ifSimpleLambda args
    then parseLambdaSimple args bodies
    else parseLambdaOpt args bodies

  and parseLambdaSimple args bodies =
    match bodies with
    | Pair (body, Nil) -> LambdaSimple (parseLambdaParams args pairToList, tag_parse_expression body)
    | _ -> LambdaSimple (parseLambdaParams args pairToList, sequencesExpr bodies)

  and parseLambdaOpt args bodies =
    match bodies with
    | Pair (body, Nil) -> LambdaOpt ((List.rev (List.tl (List.rev (parseLambdaParams args pairToListOpt)))),
                                     (List.hd (List.rev (parseLambdaParams args pairToListOpt))), (tag_parse_expression body))
    | _ -> LambdaOpt ((List.rev (List.tl (List.rev (parseLambdaParams args pairToListOpt)))),
                      (List.hd (List.rev (parseLambdaParams args pairToListOpt))), sequencesExpr bodies)

  and pairToList pairs = 
    match pairs with
    | Nil -> []
    | Pair (left, right) -> left :: (pairToList right)
    | _ -> raise X_syntax_error

  and parseLambdaParams params pairToListFunc =
    let lst = pairToListFunc params in
    List.map (fun param ->
        match param with
        | Symbol str ->
          if not (varParser str)
          then str
          else raise X_syntax_error
        | _ -> raise X_syntax_error)
      (duplicateCheck lst lst)

  and duplicateCheck list originalList = 
    if list = []
    then originalList
    else
    if List.mem (List.hd list) (List.tl list)
    then raise X_syntax_error
    else duplicateCheck (List.tl list) originalList

  and pairToListOpt pairs =
    match pairs with
    | Pair (left, Pair (left2, right2)) -> left :: (pairToListOpt (Pair (left2, right2)))  
    | Pair (left, right) -> left :: [right]
    | Symbol x -> [Symbol x]
    | _ -> raise X_syntax_error

  and parseOr args =
    match args with
    | Nil -> Const (Sexpr (Bool false))
    | Pair (x, Nil) -> tag_parse_expression x
    | _ -> Or (tag_parse_expressions (pairToList args))

  and parseAnd args =
    match args with
    | Nil -> Const (Sexpr (Bool true))
    | Pair (x, Nil) -> tag_parse_expression x
    | Pair (x, nextArgs) -> If (tag_parse_expression x, parseAnd nextArgs, Const (Sexpr (Bool false)))
    | _ -> raise X_syntax_error

  and tag_parse_expressions sexprs = List.map tag_parse_expression sexprs
  ;;


end;; (* struct Tag_Parser *)