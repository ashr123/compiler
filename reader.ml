(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
*)

#use "pc.ml";;
open PC;;
exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type number =
  | Int of int
  | Float of float;;

type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | Vector of sexpr list;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool b1, Bool b2 -> b1 = b2
  | Nil, Nil -> true
  | Number (Float f1), Number (Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number (Int n1), Number (Int n2) -> n1 = n2
  | Char c1, Char c2 -> c1 = c2
  | String s1, String s2 -> s1 = s2
  | Symbol s1, Symbol s2 -> s1 = s2
  | Pair (car1, cdr1), Pair (car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | Vector l1, Vector l2 -> List.for_all2 sexpr_eq l1 l2
  | _ -> false;;

module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
  let normalize_scheme_symbol str =
    let s = string_to_list str in
    if (andmap
          (fun ch -> (ch = (lowercase_ascii ch)))
          s) then str
    else Printf.sprintf "|%s|" str;;

  let _Bool_ =
    let _false_ = pack (word_ci "#f") (fun _ -> Bool false) in
    let _true_ = pack (word_ci "#t") (fun _ -> Bool true) in
    disj _false_ _true_;;
  (*test_string _bool_ "#fshe is a nice guy!";;*)

  let _CharPrefix_ = word "#\\";;
  let _VisibleSimpleChar_ = range_ci '!' '~';;
  let _DigitChar_ = range '0' '9';;
  let _af_ = range_ci 'a' 'f'
  let _HexDigitChar_ = disj _DigitChar_ _af_;;
  let _VisibleChar_ = pack (caten _CharPrefix_ _VisibleSimpleChar_) (fun (_, s) -> Char s);;

  let _HexChar_ = pack (caten (caten (char_ci 'x') _HexDigitChar_) _HexDigitChar_)
      (fun ((_, a), b) -> Char (Char.chr (int_of_string ("0x"^(String.make 1 a)^(String.make 1 b)))));;

  (* _HexChar_ (string_to_list "xff");; *)

  let _NamedCharacters_ =
    let _newline_ = pack (word_ci "#\\newline") (fun _-> Char '\n')
    and _return_ = pack (word_ci "#\\return") (fun _-> Char '\r')
    and _page_ = pack (word_ci "#\\page") (fun _ -> Char '\012')
    and _space_ = pack (word_ci "#\\space") (fun _ -> Char ' ')
    and _nul_ = pack (word_ci "#\\nul") (fun _ -> Char '\000')
    and _tab_ = pack (word_ci "#\\tab") (fun _-> Char  '\t') in
    disj (disj (disj (disj (disj _tab_ _newline_) _return_) _space_) _page_) _nul_;;

  (* test_string _HexChar_ "#\\newline";; *)

  let _PrefixWithHexChar_ = pack (caten (word_ci "#\\") _HexChar_)(fun (_, s) ->  s);;

  let _Char_ = disj_list [_NamedCharacters_ ; _PrefixWithHexChar_ ; _VisibleChar_];;

  let _Digit_ = pack _DigitChar_ (fun s -> int_of_char s - (int_of_char '0'));;

  let _Natural_ =
    let make_nt_natural () = plus _Digit_ in
    pack (make_nt_natural ())(fun s -> List.fold_left
                                 (fun a b -> 10 * a + b)
                                 0
                                 s);;
  (* test_string _Natural_ "099";; *)

  let _PositiveInteger_ = pack (caten (char '+') _Natural_) (fun (_, s) -> s);;
  (* test_string _PositiveInteger_ "+099";; *)

  let _NegativeInteger_ = pack (caten (char '-') _Natural_) (fun (_, s) -> s * (-1));;
  (* test_string _NegativeInteger_ "-099";; *)

  let _Integer_ = pack (disj_list [_NegativeInteger_ ; _PositiveInteger_ ; _Natural_ ])(fun s -> s);;


  let _HexDigit_ = pack _HexDigitChar_ (fun s -> float_of_string ("0x" ^ String.make 1 s));;

  let _HexNatural_ = pack (plus  _HexDigitChar_ )(fun s -> int_of_string ("0x" ^ list_to_string s));;

  let _HexNumNegative_ = pack (caten (char '#') (caten (char_ci 'x')(caten (char '-') _HexNatural_))) (fun (_, (_, (_, s)))-> (-1) * s );;
  let _HexNumPositive_ = pack (caten (char '#') (caten (char_ci 'x')(caten (char '+') _HexNatural_))) (fun (_, (_, (_, s)))-> s );;
  let _HexNatural2_ = pack (caten (char '#') (caten (char_ci 'x') _HexNatural_)) (fun ((_, (_, s)))-> s);;


  let _HexInteger_ = disj_list [_HexNumNegative_ ; _HexNumPositive_ ; _HexNatural2_];;

  (* test_string _Integer_ "#xFa";;
     test_string _Integer_ "#x+Fa";;
     test_string _Integer_ "#x-aaa";;
     test_string _Integer_ "+0003490";;
     test_string _Integer_ "-0098978";;
     test_string _Integer_ "3249283";; *)

  let _FloatSS_ = pack (caten (char '-') (caten _Integer_ (caten (char '.') _Natural_)) )
      (fun (_,(a, (_, s))) -> -1.0 *. float_of_string (string_of_int a ^ "." ^ string_of_int s));;  

  let _Float_ = pack (caten _Integer_ (caten (char '.') _Natural_)) 
      (fun (a, (_, s)) -> float_of_string (string_of_int a ^ "." ^ string_of_int s));;

  let _HexFloat_ = pack (caten (word_ci "#x") (caten (plus _HexDigitChar_) (caten (char '.') (plus _HexDigitChar_))))
      (fun (_,(a, (_, s))) -> float_of_string ("0x" ^ list_to_string a ^ "." ^ list_to_string s));;

  let _HexFloatPlus_ = pack (caten (word_ci "#x+") (caten (plus _HexDigitChar_) (caten (char '.') (plus _HexDigitChar_))))
      (fun (_,(a, (_, s))) -> float_of_string ("0x" ^ list_to_string a ^ "." ^ list_to_string s));;

  let _HexFloatMinus_ = pack (caten (word_ci "#x-") (caten (plus _HexDigitChar_) (caten (char '.') (plus _HexDigitChar_))))
      (fun (_,(a, (_, s))) -> -1.0 *. float_of_string ("0x" ^ list_to_string a ^ "." ^ list_to_string s));;


  (* test_string _Float_ "#x-10.99";;
     test_string _HexFloat_ "#x-af.#x02";; *)

  let _int_ = pack (disj _HexInteger_ _Integer_) (fun s -> Int s);;

  let _float_ = pack (disj_list [_HexFloatPlus_; _HexFloatMinus_; _HexFloat_; _FloatSS_ ; _Float_]) (fun s -> Float s);;

  let _ScientificNotation_ = pack (caten (disj _float_ _int_) (caten (char_ci 'e') _Integer_))
      (fun (a, (_, b)) ->
         match a with
         | Int(a) -> Float ((float_of_int a) *. (10.0**(float_of_int b)))
         | Float(a) -> Float ( a *. (10.0**(float_of_int b))));;

  let _Number_ = pack (disj_list [_ScientificNotation_ ; _float_; _int_]) (fun s -> Number s)  ;;

  (* 
test_string _Number_ "+0003490";;
test_string _Number_ "+055.555";;
test_string _Number_ "#x-af.#x02";; *)

  let _StringLiteralChar_ = pack (diff nt_any (disj (char '\\') (char '\"'))) (fun s -> String.make 1 s);;

  let _StringMetaChar_ =
    let backSlash = pack (word "\\\\") (fun _ -> "\\\\")
    and shmulic = pack (word "\\\"") (fun _ -> "\\\"")
    and tab = pack (word_ci "\\t") (fun _ -> "\\t") 
    and f = pack (word_ci "\\f") (fun _ -> "\\f") (*TODO *)
    and enter = pack (word_ci "\\n") (fun _ -> "\\n")
    and r = pack (word_ci "\\r") (fun _ -> "\\r") in
    disj_list [backSlash; shmulic; tab; f; enter; r];;

  let _HexChar2_ = pack (caten (caten (char_ci 'x') _HexDigitChar_) _HexDigitChar_)
      (fun ((_, a), b) -> Char.chr (int_of_string ("0x"^(String.make 1 a)^(String.make 1 b))));;

  let _StringHexChar_ = pack (caten (word "\\") (caten _HexChar2_ (word ";"))) (fun (_, (s,_)) -> String.make 1 s);;

  (* test_string _StringMetaChar_ "\\t";; *)
  (* test_string _StringHexChar_ "\\xFa";; *)

  let _SymbolChar_ = disj_list [_DigitChar_; range_ci 'a' 'z'; char '!'; char '$'; char '^'; char '*'; 
                                char '-'; char '_'; char '='; char '+'; char '<'; char '>'; char '?'; char '/'; char ':'];;

  let _Symbol_ = pack (plus _SymbolChar_) (fun s -> Symbol (list_to_string (List.map (fun c -> lowercase_ascii c) s)));;

  let _StringChar_ = disj_list [_StringMetaChar_; _StringHexChar_; _StringLiteralChar_];;

  let _append_ a b = a ^ b;;

  let _String_ = pack (caten (char '"') (caten (star _StringChar_) (char '"'))) (fun (_, (s, _)) -> String (List.fold_right _append_ s ""));;
  (* _String_ (string_to_list "\"xff\"");; *)

  let _Nil_ = pack (word "()") (fun _ -> Nil);;

  let _Test_ = pack (word "'( ...") (fun _ -> Nil);;
  (* test_string _ScientificNotation_ "3.12345e3";; *)

  let _Whitespace_ = range '\000' ' ';;

  (* test_string _Sexpr_ "3.12345e3";; *)

  let _FoldPairList_ pairList = List.map (fun (se, charList) -> se) pairList;;

  let rec _Sexpr_ ss =
    let _disj_ = disj_list [_Bool_; _Nil_; _Number_; _Char_; _String_; _Symbol_; _Quoted_; _QQuoted_; _UnquotedSpliced_; _Unquoted_ ;_Vector_; _List_; _DottedList_; _ListB_; _DottedListB_ ; _Test_] in 
    _disj_ ss

  and _List_ ss = pack (caten (caten (char '(') (star nt_whitespace)) (caten (plus (caten  _Sexpr_ (star nt_whitespace))) (char ')')))
      (fun (_, (s, _)) -> List.fold_right (fun n1 n2 -> Pair (n1, n2)) (_FoldPairList_ s) Nil) ss

  and _DottedList_ ss = pack (caten (caten (char '(') (star nt_whitespace)) (caten (caten (caten (caten (plus (caten  _Sexpr_ (star nt_whitespace))) (char '.')) (star nt_whitespace)) (caten  _Sexpr_ (star nt_whitespace))) (char ')')))
      (fun (_, (((((s, _), _), (e, _)), _))) -> List.fold_right (fun n1 n2 -> Pair (n1, n2)) (_FoldPairList_ s) e) ss

  and _Vector_ ss = pack (caten (caten (word "#(") (star nt_whitespace)) (caten (plus (caten  _Sexpr_ (star nt_whitespace))) (char ')')))
      (fun (_, (s, _)) -> Vector (_FoldPairList_ s)) ss

  and _ListB_ ss = pack (caten (caten (char '[') (star nt_whitespace)) (caten (plus (caten  _Sexpr_ (star nt_whitespace))) (char ']')))
      (fun (_, (s, _)) -> List.fold_right (fun n1 n2 -> Pair (n1, n2)) (_FoldPairList_ s) Nil) ss

  and _DottedListB_ ss = pack (caten (caten (char '[') (star nt_whitespace)) (caten (caten (caten (caten (plus (caten  _Sexpr_ (star nt_whitespace))) (char '.')) (star nt_whitespace)) (caten  _Sexpr_ (star nt_whitespace))) (char ']')))
      (fun (_, (((((s, _), _), (e, _)), _))) -> List.fold_right (fun n1 n2 -> Pair (n1, n2)) (_FoldPairList_ s) e) ss

  and _Quoted_ ss = pack (caten (char '\'') _Sexpr_) (fun (_, s) -> Pair (Symbol "quote", Pair (s, Nil))) ss

  and _QQuoted_ ss = pack (caten (char '`') _Sexpr_) (fun (_, s) -> Pair (Symbol "quasiquote", Pair (s, Nil))) ss

  and _UnquotedSpliced_ ss = pack (caten (word ",@") _Sexpr_) (fun (_, s) -> Pair (Symbol "unquote-splicing", Pair (s, Nil))) ss

  and _Unquoted_ ss = pack (caten (char ',') _Sexpr_) (fun (_, s) -> Pair (Symbol "unquote", Pair (s, Nil))) ss
  ;;

  let _Whitespaces_ = pack (caten(caten (star nt_whitespace) _Sexpr_) (star nt_whitespace)) (fun ((_, s), _) -> s);;


  let read_sexpr string  = let (sl, _) = _Whitespaces_ (string_to_list string) in sl;;

  let read_sexprs string = let (sl, _) = (star _Whitespaces_) (string_to_list string) in sl;;

end;; (* struct Reader *)

Reader.read_sexpr "\"This is a string with \\f\"";;