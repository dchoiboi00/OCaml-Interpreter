(*******************************************************************
    General-purpose LL(1) parser generator and parse tree generator,
    with (skeleton of) a syntax tree builder and interpreter for an
    extended calculator language.

    (c) Michael L. Scott, 2023
    For use by students in CSC 2/454 at the University of Rochester,
    during the Fall 2023 term.  All other use requires written
    permission of the author.

    If compiled and run, will execute "main()".
    Alternatively, can be "#use"-ed (or compiled and then "#load"-ed)
    into the top-level interpreter.
 *******************************************************************)

open List;;
(* The List library includes a large collection of useful functions.
   In the provided code, I've used assoc, exists, filter, find,
   find_opt, fold_left, hd, length, map, and rev.
*)

open Str;;      (* for regexp and split *)
(* The Str library provides a few extra string-processing routines.
   In particular, it provides "split" and "regexp", which I use to break
   program input into whitespace-separated words.  Note, however, that
   this library is not automatically available.  If you are using the
   top-level interpreter, you have to say
        #load "str.cma";;
   before you say
        #use "interpreter.ml";;
   If you are generating an executable from the shell, you have to
   include the library name on the command line:
        ocamlc -o interpreter str.cma interpreter.ml
*)

(*******************************************************************
    Preliminaries.
 *******************************************************************)

(* Surprisingly, compose isn't built in.  It's included in various
   widely used commercial packages, but not in the core libraries. *)
let compose f g x = f (g x);;

(* is e a member of list l? *)
let member e l = exists ((=) e) l;;

(* OCaml has a built-in quicksort; this was just an exercise. *)
let rec sort l =
  let rec partition pivot l left right =
    match l with
    | []        -> (left, right)
    | c :: rest -> if c < pivot
                   then partition pivot rest (c :: left) right
                   else partition pivot rest left (c :: right) in
  match l with
  | []        -> l
  | h :: []   -> l
  | h :: rest -> let (left, right) = partition h rest [] [] in
                 (sort left) @ [h] @ (sort right);;

(* Leave only one of any consecutive identical elements in list. *)
let rec unique l =
  match l with
  | []             -> l
  | h :: []        -> l
  | a :: b :: rest -> if a = b (* structural eq *)
                      then unique (b :: rest)
                      else a :: unique (b :: rest);;

let unique_sort l = unique (sort l);;

(* Join two strings with a given separator in between
   -- but only if both are non-null. *)
let str_cat sep a b =
  match (a, b) with
  | (a, "") -> a
  | ("", b) -> b
  | (_, _) -> a ^ sep ^ b;;

(*******************************************************************
    Grammars, Parser Generator, Scanner, and Parser.

    For this course we are using a single grammar -- for the extended
    calcular language.  It was easiest for me to build the project,
    however, if I could experiment with changes to the language without
    having to change the parser by hand.  So we have here a complete
    parser generator.
 *******************************************************************)

 (* symbol_production is a tuple of two component:
    First component: string
    Second component: a list for (string list), basically a list for lists of strings
 *)
type symbol_productions = (string * string list list);;

(* a list of symbol_productions *)
type grammar = symbol_productions list;;

(* parse_table is a list of tuples that contains two component:
   First component: string (nt)
   Second component: a list of a a tuple that contains two component: (predicts sets)
        each tuple is:
        First component: string list  ex: beginning of tuple ( [int, real, id, read]
        Second component: string list ex:                      [S, SL] or [epsilon] ) end of tuple

        ex:
        nt = SL
        parse_table = 
        [
        ("SL", [ ([int, real, id, read], [S, SL]),
                ([fi, od, $$], [epsilon]) 
              ]
        ),
        (...),
        (...)
        ]
*)
type parse_table = (string * (string list * string list) list) list;;
(*                  nt        predict_set   rhs *)

let calc_gram : grammar =
  [ ("P",  [["SL"; "$$"]])
  ; ("SL", [["S"; "SL"]; []])
  ; ("S",  [ ["id"; ":="; "E"]; ["read"; "id"]; ["write"; "E"]])
  ; ("E",  [["T"; "TT"]])
  ; ("T",  [["F"; "FT"]])
  ; ("TT", [["AO"; "T"; "TT"]; []])
  ; ("FT", [["MO"; "F"; "FT"]; []])
  ; ("AO", [["+"]; ["-"]])
  ; ("MO", [["*"]; ["/"]])
  ; ("F",  [["id"]; ["num"]; ["("; "E"; ")"]])
  ];;

let ecg : grammar =             (* extended calculator grammar *)
  [ ("P",  [["SL"; "$$"]])
  ; ("SL", [["S"; "SL"]; []])
  ; ("S",  [ ["int"; "id"; ":="; "E"]; ["real"; "id"; ":="; "E"]
           ; ["id"; ":="; "E"]; ["read"; "TP"; "id"]; ["write"; "E"]
           ; ["if"; "C"; "SL"; "fi"]; ["do"; "SL"; "od"]; ["check"; "C"]
           ])
  ; ("TP", [["int"]; ["real"]; []])
  ; ("C",  [["E"; "RO"; "E"]])
  ; ("RO", [["=="]; ["!="]; ["<"]; [">"]; ["<="]; [">="]])
  ; ("E",  [["T"; "TT"]])
  ; ("TT", [["AO"; "T"; "TT"]; []])
  ; ("T",  [["F"; "FT"]])
  ; ("FT", [["MO"; "F"; "FT"]; []])
  ; ("F",  [["id"]; ["i_num"]; ["r_num"]; ["("; "E"; ")"]
           ; ["trunc"; "("; "E"; ")"]; ["float"; "("; "E"; ")"]])
  ; ("AO", [["+"]; ["-"]])
  ; ("MO", [["*"]; ["/"]])
  ];;

(* Return all individual productions in grammar. *)
let productions gram : (string * string list) list =
  let prods (lhs, rhss) = map (fun rhs -> (lhs, rhs)) rhss in
  fold_left (@) [] (map prods gram);;

(* Return all symbols in grammar. *)
let gsymbols gram : string list =
  unique_sort
    (fold_left (@) [] (map (compose (fold_left (@) []) snd) gram));;

(* Return all elements of l that are not in to_exclude.
   Assume that both lists are sorted. *)
let list_minus l to_exclude =
  let rec helper rest te rtn =
    match rest with
    | []     -> rtn
    | h :: t -> match te with
                | []       -> (rev rest) @ rtn
                | h2 :: t2 -> match Stdlib.compare h h2 with
                              | -1 -> helper t te (h :: rtn)
                              |  0 -> helper t t2 rtn
                              |  _ -> helper rest t2 rtn in
  rev (helper l to_exclude []);;

(* Return just the nonterminals. *)
let nonterminals gram : string list = map fst gram;;

(* Return just the terminals. *)
let terminals gram : string list =
    list_minus (gsymbols gram) (unique_sort (nonterminals gram));;

(* Return the start symbol.  Throw exception if grammar is empty. *)
let start_symbol gram : string = fst (hd gram);;

let is_nonterminal e gram = member e (nonterminals gram);;

let is_terminal e gram = member e (terminals gram);;

let union s1 s2 = unique_sort (s1 @ s2);;

(* Return suffix of lst that begins with first occurrence of sym
   (or [] if there is no such occurrence). *)
let rec suffix sym lst = 
  match lst with
  | [] -> []
  | h :: t -> if h = sym (* structural eq *)
              then lst else suffix sym t;;

(* Return a list of pairs.
   Each pair consists of a symbol A and a list of symbols beta
   such that for some alpha, A -> alpha B beta. *)
type right_context = (string * string list) list;;
let get_right_context (b:string) gram : right_context =
  fold_left (@) []
            (map (fun prod ->
                    let a = fst prod in
                    let rec helper accum rhs =
                      let b_beta = suffix b rhs in
                      match b_beta with
                      | [] -> accum
                      | x :: beta  -> (* assert x = b *)
                                      helper ((a, beta) :: accum) beta in
                    helper [] (snd prod))
                 (productions gram));;

(********
    Parser generator starts here.
********)

type symbol_knowledge = string * bool * string list * string list;;
type knowledge = symbol_knowledge list;;
let symbol_field (s, e, fi, fo) = s;;
let eps_field (s, e, fi, fo) = e;;
let first_field (s, e, fi, fo) = fi;;
let follow_field (s, e, fi, fo) = fo;;

let initial_knowledge gram : knowledge =
  map (fun a -> (a, false, [], [])) (nonterminals gram);;

let get_symbol_knowledge (a:string) (kdg:knowledge) : symbol_knowledge =
  find (fun (s, e, fi, fo) -> s = a) kdg;;

(* Can word list w generate epsilon based on current estimates?
   if w is an empty list, yes
   if w is a single terminal, no
   if w is a single nonterminal, look it up
   if w is a non-empty list, "iterate" over elements *)
let rec generates_epsilon (w:string list) (kdg:knowledge) gram : bool =
  match w with
  | [] -> true
  | h :: t -> if is_terminal h gram then false
              else eps_field (get_symbol_knowledge h kdg)
                   && generates_epsilon t kdg gram;;

(* Return FIRST(w), based on current estimates.
   if w is an empty list, return []  [empty set]
   if w is a single terminal, return [w]
   if w is a single nonterminal, look it up
   if w is a non-empty list, "iterate" over elements *)
let rec first (w:string list) (kdg:knowledge) gram : (string list) =
  match w with
  | [] -> []
  | x :: _ when is_terminal x gram -> [x]
  | x :: rest -> let s = first_field (get_symbol_knowledge x kdg) in
                 if generates_epsilon [x] kdg gram
                 then union s (first rest kdg gram)
                 else s;;

let follow (a:string) (kdg:knowledge) : string list =
  follow_field (get_symbol_knowledge a kdg);;

let rec map3 f l1 l2 l3 =
  match (l1, l2, l3) with
  | ([], [], []) -> []
  | (h1 :: t1, h2 :: t2, h3 :: t3) -> (f h1 h2 h3) :: map3 f t1 t2 t3
  | _ -> raise (Failure "mismatched_lists in map3");;

(* Return knowledge structure for grammar.
   Start with (initial_knowledge grammar) and "iterate",
   until the structure doesn't change.
   Uses (get_right_context B gram), for all nonterminals B,
   to help compute follow sets. *)
let get_knowledge gram : knowledge =
  let nts : string list = nonterminals gram in
  let right_contexts : right_context list
     = map (fun s -> get_right_context s gram) nts in
  let rec helper kdg =
    let update : symbol_knowledge -> symbol_productions
                   -> right_context -> symbol_knowledge
          = fun old_sym_kdg sym_prods sym_right_context ->
      let my_first s = first s kdg gram in
      let my_eps s = generates_epsilon s kdg gram in
      let filtered_follow p = if my_eps (snd p)
                              then (follow (fst p) kdg)
                              else [] in
      (
        symbol_field old_sym_kdg,       (* nonterminal itself *)
        (eps_field old_sym_kdg)         (* previous estimate *)
            || (fold_left (||) false (map my_eps (snd sym_prods))),
        union (first_field old_sym_kdg) (* previous estimate *)
            (fold_left union [] (map my_first (snd sym_prods))),
        union (union
                (follow_field old_sym_kdg)  (* previous estimate *)
                (fold_left union [] (map my_first
                                      (map (fun p ->
                                              match snd p with
                                              | [] -> []
                                              | h :: t -> [h])
                                           sym_right_context))))
              (fold_left union [] (map filtered_follow sym_right_context))
      ) in    (* end of update *)
    let new_kdg = map3 update kdg gram right_contexts in
    (* body of helper: *)
    if new_kdg = kdg then kdg else helper new_kdg in
  (* body of get_knowledge: *)
  helper (initial_knowledge gram);;

let get_parse_table (gram:grammar) : parse_table =
  let kdg = get_knowledge gram in
  map (fun (lhs, rhss) ->
        (lhs, (map (fun rhs ->
                      (union (first rhs kdg gram)
                             (if (generates_epsilon rhs kdg gram)
                              then (follow lhs kdg) else []),
                      rhs))
                   rhss)))
      gram;;

type row_col = int * int;;      (* source location *)
let complaint (loc:row_col) (msg:string) =
  let (l, c) = loc in
  Printf.sprintf " line %d, col %d: %s" l c msg;;

(* Convert string to list of chars, each tagged with row and column.
   Also return number of lines. *)
let explode_and_tag (s:string) : (char * row_col) list * int =
  let rec exp i r c l =
    if i = String.length s then l
    else
      let (r2, c2) = if s.[i] = '\n' then (r+1, 1) else (r, c+1) in
      exp (i+1) r2 c2 ((s.[i], (r, c)) :: l) in
  let chars = exp 0 1 1 [] in
  let rows = match chars with
             | [] -> 0
             | (_, (r, _))::t -> r in
  (rev chars, rows)

(* Convert list of char to string.
   (This uses imperative features.  It used to be a built-in.) *)
let implode (l:char list) : string =
  let res = Bytes.create (length l) in
  let rec imp i l =
    match l with
    | [] -> Bytes.to_string res
    | c :: l -> Bytes.set res i c; imp (i + 1) l in
  imp 0 l;;

(********
    Scanner.  Currently specific to the extended calculator language.
********)

type token = string * string * row_col;;
(*         category * name   * row+column *)

let tokenize (program:string) : token list =
  let (chars, num_lines) = explode_and_tag program in
  let get_id prog =
    let rec gi tok p =
        match p with
        | (c, _) :: rest when (('a' <= c && c <= 'z')
                               || ('A' <= c && c <= 'Z')
                               || ('0' <= c && c <= '9') || (c = '_'))
            -> gi (c :: tok) rest
        | _ -> (implode (rev tok), p) in
    gi [] prog in
  (* get_num matches digit*(.digit*((e|E)(+|-)?digit+)?)?
     We're pickier below -- insist on a digit on at least one side of the . *)
  let get_num prog =        (* integer or real *)
    let get_int prog =          (* eat digit* *)
      let rec gi tok p =
          match p with
          | (c, _) :: rest when ('0' <= c && c <= '9')
              -> gi (c :: tok) rest
          | _ -> (implode (rev tok), p) in
      gi [] prog in
    let get_exp prog =          (* eat (e|E)(+|-|epsilon)digit+ *)
      match prog with
      | (e, eloc) :: r1 when (e = 'e' || e = 'E')
          -> (match r1 with
              | (s, _) :: (d, dloc) :: r2
                    when (s = '+' || s = '-') && ('0' <= d && d <= '9')
                -> let (pow, r3) = get_int ((d, dloc) :: r2) in
                   ((String.make 1 e) ^ (String.make 1 s) ^ pow, r3)
              | (d, dloc) :: r2 when ('0' <= d && d <= '9')
                -> let (pow, r3) = get_int ((d, dloc) :: r2) in
                   ((String.make 1 e) ^ pow, r3)
              | _ -> ("error", (e, eloc) :: r1))
      | _ -> ("", prog) in
    let (whole, r1) = get_int prog in
    match r1 with
    | ('.', _) :: r2
        -> let (frac, r3) = get_int r2 in
           let (exp, r4) = get_exp r3 in
           (whole ^ "." ^ frac ^ exp, r4)
    | _ -> (whole, r1) in
  let rec get_error tok prog =
    match prog with
    | [] -> (implode (rev tok), prog)
    | (c, _) :: rest ->
        match c with
        | ';' | ':' | '+' | '-' | '*' | '/' | '(' | ')'
        | '_'| '<' | '>' | '=' | 'a'..'z' | 'A'..'Z' | '0'..'9'
            -> (implode (rev tok), prog)
        | _ -> get_error (c :: tok) rest in
  let rec skip_space prog =
    match prog with
    | [] -> []
    | (c, _) :: rest -> if (c = ' ' || c = '\n' || c = '\r' || c = '\t')
                        then skip_space rest else prog in
  let rec tkize toks prog =
    match prog with
    | []                           -> ((("$$", (num_lines + 1, 0)) :: toks), [])
    | ('\n', _) :: rest
    | ('\r', _) :: rest
    | ('\t', _) :: rest
    | (' ', _)  :: rest            -> tkize toks (skip_space prog)
    | (':', l) :: ('=', _) :: rest -> tkize ((":=", l) :: toks) rest
    | ('+', l) :: rest             -> tkize (("+", l)  :: toks) rest
    | ('-', l) :: rest             -> tkize (("-", l)  :: toks) rest
    | ('*', l) :: rest             -> tkize (("*", l)  :: toks) rest
    | ('/', l) :: rest             -> tkize (("/", l)  :: toks) rest
    | ('(', l) :: rest             -> tkize (("(", l)  :: toks) rest
    | (')', l) :: rest             -> tkize ((")", l)  :: toks) rest
    | ('<', l) :: ('=', _) :: rest -> tkize (("<=", l) :: toks) rest
    | ('<', l) :: rest             -> tkize (("<", l)  :: toks) rest
    | ('>', l) :: ('=', _) :: rest -> tkize ((">=", l) :: toks) rest
    | ('>', l) :: rest             -> tkize ((">", l)  :: toks) rest
    | ('=', l) :: ('=', _) :: rest -> tkize (("==", l) :: toks) rest
    | ('!', l) :: ('=', _) :: rest -> tkize (("!=", l) :: toks) rest
    | (h, l) :: t ->
        match h with
        | '.' | '0'..'9' -> let (nm, rest) = get_num prog in
                            tkize ((nm, l) :: toks) rest
        | 'a'..'z'
        | 'A'..'Z'
        | '_'            -> let (nm, rest) = get_id prog in
                            tkize ((nm, l) :: toks) rest
        | x              -> let (nm, rest) = get_error [x] t in
                            tkize ((nm, l) :: toks) rest in
  let (toks, _) = (tkize [] chars) in
  let categorize tok =
    let (nm, loc) = tok in
    match nm with
    | "check" | "do"   | "float" | "fi"    | "if"    | "int"   
    | "od"    | "read" | "real"  | "trunc" | "write"
    | ":="    | "+"    | "-"     | "*"     | "/"     | "("  | ")"
    | "<"    | "<="    | ">"     | ">="    | "!="    | "==" | "$$"
        -> (nm, nm, loc)
    | _ -> match nm.[0] with
           | '.' -> (try    (* insist on digit on at least one side of . *)
                       if ('0' <= nm.[1] && nm.[1] <= '9')
                         then ("r_num", nm, loc)
                         else ("error", nm, loc)
                     with Invalid_argument(_) -> ("error", nm, loc))
           | '0'..'9' -> if String.contains nm '.'
                            then ("r_num", nm, loc)
                            else ("i_num", nm, loc)
           | 'a'..'z'
           | 'A'..'Z' | '_' -> ("id", nm, loc)
           | _ -> ("error", nm, loc) in
  map categorize (rev toks);;

(*******************************************************************
    Parser.  The main parse routine returns a parse tree (or PT_error if
    the input program is syntactically invalid).  To build that tree it
    employs a simplified version of the "attribute stack" described in
    Section 4.5.2 (pages 50-55) on the PLP companion site.

    When it predicts A -> B C D, the parser pops A from the parse stack
    and then, before pushing D, C, and B (in that order), it pushes a
    number (in this case 3) indicating the length of the right hand side.
    It also pushes A into the attribute stack.

    When it matches a token, the parser pushes this into the attribute
    stack as well.

    Finally, when it encounters a number (say k) in the stack (as opposed
    to a character string), the parser pops k+1 symbols from the
    attribute stack, joins them together into a list, and pushes the list
    back into the attribute stack.

    These rules suffice to accumulate a complete parse tree into the
    attribute stack at the end of the parse.

    Note that everything is done functionally.  We don't really modify
    the stacks; we pass new versions to tail recursive routines.
 *******************************************************************)

(* Extract grammar from parse-tab, so we can invoke the various routines
   that expect a grammar as argument. *)
let grammar_of (parse_tab:parse_table) : grammar =
  map (fun p -> (fst p,
                 (fold_left (@)
                            []
                            (map (fun (a, b) -> [b]) (snd p)))))
      parse_tab;;

type parse_tree =   (* among other things, parse_trees are *)
| PT_error          (* the elements of the attribute stack *)
| PT_id of (string * row_col)
| PT_int of (string * row_col)
| PT_real of (string * row_col)
| PT_term of (string * row_col)
| PT_nt of (string * row_col * parse_tree list);;
    
(* Pop rhs-len + 1 symbols off the attribute stack,
   assemble into a production, and push back onto the stack. *)
let reduce_1_prod (astack:parse_tree list) (rhs_len:int) : parse_tree list =
  let rec helper atk k prod =
    match (k, atk) with
    | (0, PT_nt(nt, loc, []) :: t) -> PT_nt(nt, loc, prod) :: t
    | (n, h :: t) when n != 0 -> helper t (k - 1) (h :: prod)
    | _ -> raise (Failure "expected nonterminal at top of astack") in
   helper astack rhs_len [];;

type parse_action = PA_error | PA_prediction of string list;;
(* Double-index to find prediction (list of RHS symbols) for
   nonterminal nt and terminal t.  Return PA_error if not found. *)
let get_parse_action (nt:string) (t:string) (parse_tab:parse_table)
    : parse_action =
  let rec helper l =
      match l with
      | [] -> PA_error
      | (fs, rhs) :: rest -> if member t fs then PA_prediction(rhs)
                             else helper rest in
  helper (assoc nt parse_tab);;

type ps_item =      (* elements of parse stack *)
| PS_end of int
| PS_sym of string;;

(* Parse program according to grammar.
   [Commented-out code would
       print predictions and matches (imperatively) along the way.]
   Return parse tree if the program is in the language; PT_error if it's not. *)
let parse (parse_tab:parse_table) (program:string) : parse_tree =
  let die loc msg =
    begin
      let (l, c) = loc in
      (* print to screen in REPL; to stderr when compiled *)
      (if !Sys.interactive then Printf.printf else Printf.eprintf)
        "syntax error at line %d, col %d: %s\n" l c msg;
      PT_error 
    end in
  let gram = grammar_of parse_tab in
  let rec helper pstack tokens astack =
    match pstack with
    | [] ->
        if tokens = [] then
          (* assert: astack is nonempty *)
          hd astack
        else die (0, 0) "extra input beyond end of program"
    | PS_end(n) :: ps_tail ->
        helper ps_tail tokens (reduce_1_prod astack n)
    | PS_sym(tos) :: ps_tail ->
        match tokens with
        | [] -> die (0, 0) "unexpected end of program"
        | (term, nm, loc) :: more_tokens ->
           (* if nm is an individual identifier or number,
              term will be a generic "id" or "i_num" or "r_num" *)
          if is_terminal tos gram then
            if tos = term then
              begin
              (*
                print_string ("   match " ^ tos);
                print_string
                    (if tos <> term      (* deep comparison *)
                         then (" (" ^ nm ^ ")") else "");
                print_newline ();
              *)
                helper ps_tail more_tokens
                       (( match term with
                          | "id"  -> PT_id(nm, loc)
                          | "i_num" -> PT_int(nm, loc)
                          | "r_num" -> PT_real(nm, loc)
                          | _     -> PT_term(nm, loc) ) :: astack)
              end
                       (* note push of nm into astack *)
            else die loc ("expected " ^ tos ^ " ; saw " ^ nm)
          else (* nonterminal *)
            match get_parse_action tos term parse_tab with
            | PA_error -> die loc ("no prediction for " ^ tos
                                   ^ " when seeing " ^ nm)
            | PA_prediction(rhs) ->
                begin
                (*
                  print_string ("   predict " ^ tos ^ " ->");
                  print_string (fold_left (fun a b -> a ^ " " ^ b) "" rhs);
                  print_newline ();
                *)
                  helper ((fold_left (@) [] 
                                    (map (fun s -> [PS_sym(s)]) rhs))
                              @ [PS_end(length rhs)] @ ps_tail)
                         tokens (PT_nt(tos, loc, []) :: astack)
                end in
  helper [PS_sym(start_symbol gram)] (tokenize program) [];;

let cg_parse_table = get_parse_table calc_gram;;

let ecg_parse_table = get_parse_table ecg;;

(*******************************************************************
    (* NOTICE *)
    
    Everything above this point in the file is complete and (I think)
    usable as-is.  The rest of the file, from here down, is a possible
    skeleton for the code you need to write.  It was extracted from the
    complete working version available as ~cs254/bin/ecl on the caug
    machines.

 *******************************************************************)

(* Syntax tree node types.
   We distinguish between statements and expressions.
   Comments below indicate what syntactic element in the source
   is associated with the location [row_col] values.
   Note that each declaration (e.g., "int foo : 3" or "read int foo")
   is turned into a _pair_ of AST nodes -- one for the declaration
   itself and one for the initialization.
*)

type ast_sl = ast_s list
and ast_s =
| AST_error
| AST_i_dec of (string * row_col)   (* id location *)
| AST_r_dec of (string * row_col)   (* id location *)
| AST_read of (string * row_col)    (* id location *)
| AST_write of (ast_e)
| AST_assign of (string * ast_e * row_col * row_col)
                                    (* id location, := location *)
| AST_if of (ast_c * ast_sl)
| AST_do of ast_sl
| AST_check of (ast_c * row_col)    (* check location *)
and ast_e =
| AST_int of (string * row_col)
| AST_real of (string * row_col)
| AST_id of (string * row_col)
| AST_float of (ast_e * row_col)    (* lparen location *)
| AST_trunc of (ast_e * row_col)    (* lparen location *)
| AST_binop of (string * ast_e * ast_e * row_col)
                                    (* op location *)
and ast_c = (string * ast_e * ast_e * row_col);;
                                    (* op location *)
  
(* Convert parse tree to syntax tree.
   Walks the parse tree using a collection of mutually recursive subroutines. *)
let rec ast_ize_prog (p:parse_tree) : ast_sl =
  (* NOTICE: your code should replace the following line *)
  match p with
  | PT_nt ("P", _, [sl; PT_term("$$", _)]) -> ast_ize_stmt_list sl
  | _ -> raise (Failure "malformed parse tree in ast_ize_prog")

and ast_ize_stmt_list (sl:parse_tree) : ast_sl =
  match sl with
  | PT_nt ("SL", _, []) -> []
  | PT_nt ("SL", _, [s; sl]) -> ast_ize_stmt s @ ast_ize_stmt_list sl
  | _ -> raise (Failure "malformed parse tree in ast_ize_stmt_list")

and ast_ize_stmt (s:parse_tree) : ast_sl =
  match s with
  (* int/real lhs := expr*)
  | PT_nt("S", _, [PT_id(lhs, vloc); PT_term(":=", aloc); expr]) ->
      [AST_assign(lhs, (ast_ize_expr expr), vloc, aloc)]
         (* vloc is the place to complain about undeclared lhs;
            aloc (:= sign) is the place to complain about a type clash *)
  | PT_nt ("S", _, [PT_term ("int", _); PT_id(lhs, vloc); PT_term(":=", aloc); expr]) ->
      [AST_i_dec(lhs, vloc); AST_assign(lhs, (ast_ize_expr expr), vloc, aloc)]
  | PT_nt ("S", _, [PT_term ("real", _); PT_id(lhs, vloc); PT_term(":=", aloc); expr]) ->
      [AST_r_dec(lhs, vloc); AST_assign(lhs, (ast_ize_expr expr), vloc, aloc)]

  (* read int/real/e id*)
  | PT_nt ("S", _, [PT_term ("read", _); PT_nt ("TP", _, PT_term ("int", _)::rest); PT_id (id, loc)]) ->
      [AST_i_dec(id, loc); AST_read (id, loc)]
  | PT_nt ("S", _, [PT_term ("read", _); PT_nt ("TP", _, PT_term ("real", _)::rest); PT_id (id, loc)]) ->
      [AST_r_dec(id, loc); AST_read (id, loc)]
  | PT_nt ("S", _, [PT_term ("read", _); PT_nt ("TP", _, []); PT_id (id, loc)]) ->
      [AST_read (id, loc)]

  (* rest of S*)
  | PT_nt ("S", _, [PT_term ("write", _); expr]) -> 
      [AST_write (ast_ize_expr expr)]
  | PT_nt ("S", _, [PT_term ("if", _); c; sl; PT_term ("fi", _)]) ->
      [AST_if (ast_ize_cond c, ast_ize_stmt_list sl)]
  | PT_nt ("S", _, [PT_term ("do", _ ); sl; PT_term ("od", _)]) ->
      [AST_do (ast_ize_stmt_list sl)]
  | PT_nt ("S", _, [PT_term ("check", loc); c]) ->
      [AST_check (ast_ize_cond c, loc)]

  | _ -> raise (Failure "malformed parse tree in ast_ize_stmt")

and ast_ize_expr (e:parse_tree) : ast_e =   (* E, T, or F *)
  match e with
  | PT_nt ("E", _, [t; tt]) ->
      ast_ize_expr_tail (ast_ize_expr t) tt
  | PT_nt ("T", _, [f; ft]) ->
      ast_ize_expr_tail (ast_ize_expr f) ft
  | PT_nt ("F", _, [PT_id (id, id_loc)]) ->
      AST_id (id, id_loc)
  | PT_nt ("F", _, [PT_int (num, num_loc)]) ->
      AST_int (num, num_loc)
  | PT_nt ("F", _, [PT_real (num, num_loc)]) ->
      AST_real (num, num_loc)
  | PT_nt ("F", _, [PT_term ("(", _); expr; PT_term (")", _)]) ->
      ast_ize_expr expr
  | PT_nt ("F", _, [PT_term ("trunc", _); PT_term("(", lparen_loc); expr; PT_term(")", _)]) ->
      AST_trunc (ast_ize_expr(expr), lparen_loc)
  | PT_nt ("F", _, [PT_term ("float", _); PT_term("(", lparen_loc); expr; PT_term(")", _)]) ->
      AST_float (ast_ize_expr(expr), lparen_loc)
  | _ -> raise (Failure "malformed parse tree in ast_ize_expr")

and ast_ize_expr_tail (lo:ast_e) (tail:parse_tree) : ast_e =   (* TT or FT *)
  (* lo is a left operand for a potential operator in tail *)
  match tail with
  | PT_nt ("TT", _, []) -> lo
  | PT_nt ("TT", _, [PT_nt ("AO", _, PT_term(ao, op_loc)::rest); t; tt]) ->
      let n = AST_binop(ao, lo, (ast_ize_expr t), op_loc) in 
      ast_ize_expr_tail n tt 
  | PT_nt ("FT", _, []) -> lo
  | PT_nt ("FT", _, [PT_nt ("MO", _, PT_term(mo, op_loc)::rest); f; ft]) ->
      let n = AST_binop(mo, lo, (ast_ize_expr f), op_loc) in 
      ast_ize_expr_tail n ft 
  | _ -> raise (Failure "malformed parse tree in ast_ize_expr_tail")

and ast_ize_cond (c:parse_tree) : ast_c =
  match c with
  | PT_nt ("C", _, [e1; PT_nt ("RO", _, PT_term(op, op_loc)::rest); e2]) ->
    (op, ast_ize_expr e1, ast_ize_expr e2, op_loc)
  | _ -> raise (Failure "malformed parse tree in ast_ize_cond")
;;

(*******************************************************************
    AST Pretty-printer.  This should be complete and usable as-is.
 *******************************************************************)

let rec pp_sl (sl:ast_sl) (ind:string) : string =
  match sl with
  | []      -> ""
  | [s]     -> pp_s s ind
  | s :: tl -> pp_s s ind ^ "\n" ^ ind ^ pp_sl tl ind

and pp_s (s:ast_s) (ind:string) : string =
  match s with
  | AST_i_dec(id, _)            -> "(int \"" ^ id ^ "\")"
  | AST_r_dec(id, _)            -> "(real \"" ^ id ^ "\")"
  | AST_read(id, _)             -> "(read \"" ^ id ^ "\")"
  | AST_write(expr)             -> "(write " ^ (pp_e expr) ^ ")"
  | AST_assign(id, expr, _, _)  -> "(:= \"" ^ id ^ "\" " ^ pp_e expr ^ ")"
  | AST_if(cond, sl)            -> "(if " ^ pp_c cond 
                                    ^ "\n" ^ ind ^ "  [ "
                                    ^ (pp_sl sl (ind ^ "    "))
                                    ^ "\n" ^ ind ^ "  ]\n" ^ ind ^ ")"
  | AST_do(sl)                  -> "(do " ^ "\n" ^ ind ^ "  [ "
                                    ^ (pp_sl sl (ind ^ "    "))
                                    ^ "\n" ^ ind ^ "  ]\n" ^ ind ^ ")"
  | AST_check(cond, _)          -> "(check " ^ pp_c cond ^ ")"
  | AST_error                   -> "error"

and pp_e (e:ast_e) : string =
  match e with
  | AST_int(num, _)          -> "\"" ^ num ^ "\""
  | AST_real(num, _)         -> "\"" ^ num ^ "\""
  | AST_id(id, _)            -> "\"" ^ id ^ "\""
  | AST_float(e, _)          -> "(float " ^ (pp_e e) ^ ")"
  | AST_trunc(e, _)          -> "(trunc " ^ (pp_e e) ^ ")"
  | AST_binop(op, lo, ro, _) -> "(" ^ op ^ " " ^ pp_e lo ^ " " ^ pp_e ro ^ ")"

and pp_c (c:ast_c) : string =
  let (op, lo, ro, _) = c in "(" ^ op ^ " " ^ pp_e lo ^ " " ^ pp_e ro ^ ")";;

let pp_p (sl:ast_sl) = print_string ("[ " ^ (pp_sl sl "  ") ^ "\n]\n");;

(*******************************************************************
    Interpreter

    Imterprets an AST with purely dynamic semantics -- nothing is
    checked ahead of time.  Catches undefined variables, redefinitions,
    and type clashes.  Also divide-by-zero and non-numeric input or
    unexpected end of input on read.  Respects scopes: each variable is
    visible only from its declaration to the end of the innermost
    statement list in which it is declared. (Question: Is it still visible after the end
    d)
 *******************************************************************)

type value =
| Ivalue of int
| Rvalue of float
| Error of string;;

type 'a stack = 'a list;;
let push (x:'a) (s:'a stack) : 'a stack = x :: s;;
let pop (s:'a stack) : 'a option * 'a stack =
  match s with
  | [] -> (None, [])
  | x :: r -> (Some x, r);;

(* Memory is a stack of scopes, with the innermost scope at the top.
   Each scope consists of a list of (name, value) pairs. *)
type memory = (string * value) list stack;;
(* memory: 
   a stack of list(scope), which the list contains tuples that has two components:
   First component: String
   Second component: value 

   first in last out
   ex: stack -> [  [(name, val),(name, value),(name, val)],  [(n, v),(n, v),(...)],  [(),(),()]  ]
                                    scope 1                         scope 2             scope 3

*)

(* push and pop but for memory type stackd *)
let new_scope (mem:memory) : memory = push [] mem;;
let end_scope (mem:memory) : memory = let (_, mem2) = pop mem in mem2;;

let name_match id = fun (sym, _) -> id = sym;;

(*  *)
let rec lookup_mem (id:string) (loc:row_col) (mem:memory) : value =
  match mem with
  | [] -> Error (complaint loc (id ^ " not found"))
  | scope :: surround ->
      match find_opt (name_match id) scope with
      | Some (_, v) -> v
      | None -> lookup_mem id loc surround;;

let insert_mem (id:string) (v:value) (mem:memory) : (memory * bool) =
  match mem with
  | [] -> raise (Failure "unexpected case")
  | scope :: surround ->
      match find_opt (name_match id) scope with
      | Some _ -> (mem, false)
      | None   -> (((id, v) :: scope) :: surround, true);;

(* Should be called only after verifying (with lookup_mem) that id is
   already present.  Throws exception if not. *)
let rec update_mem (id:string) (v:value) (mem:memory) : memory =
  match mem with
  | [] -> raise (Failure (id ^ " not present"))
  | scope :: surround ->
      match find_opt (name_match id) scope with
      | Some _ -> ((id, v) :: (filter (fun (sym, _) -> id <> sym) scope))
                   :: surround
      | None   -> scope :: (update_mem id v surround);;

type status =
| Good
| Bad       (* run-time error *)
| Done;;    (* failed check *)

(* Input to a calculator program is just a sequence of numbers.  We use
    the standard Str library to split the input string into whitespace-
    separated words, each of which is subsequently checked for validity. *)


(* inp becomes a list of strings of the inputs(tokens) we splitted 
   let outp be what's return from calling interpret_sl with 

*)

let rec interpret (ast:ast_sl) (full_input:string) : string =
  let inp = split (regexp "[ \t\n\r]+") full_input in
  let (_, _, _, outp) = interpret_sl 0 true ast [[]] inp [] in
    (fold_left (str_cat " ") "" outp) ^ "\n"

(* iter1 indicates whether this is the first time this statement list
   has executed in a fresh scope.  It's false for the second and
   subsequent iterations of a do loop. *)

   (* sl will be a list of ast_s
    base case: when sl is empty, we just return the current output  
    else: 
    we split current sl into h and t
    h is the most nearest statement node, and t is the rest of statement list (statement nodes)
   
   *)
and interpret_sl (loop_count:int) (iter1:bool) (sl:ast_sl) (mem:memory)
                 (inp:string list) (outp:string list)
    : status * memory * string list * string list =
    (*  ok?   new_mem   new_input     new_output *)
  match sl with
  | [] -> (Good, mem, inp, outp)
  | s::sl -> 
      let (curr_status, m, i, o) = interpret_s loop_count iter1 s mem inp outp in
      (*
      Printf.printf "Statement finished: %s\n" (statement_to_string s);
      Printf.printf "Memory After: %s\n\n" (memory_to_string m); 
      *)

      (* Good: keep interpreting, no errors so far
         Bad: saw an error, stop the program and print where we caught the error
         Done: check statement returned false, stop the do-loop statement list   
      *)
      (match curr_status with
      | Good -> interpret_sl loop_count iter1 sl m i o
      | Bad -> (Bad, m, i, o)
      | Done -> (Done, m, i, o)
      )

(* Helpful functions for debugging*)
and memory_to_string (mem: memory): string =
  let mem_str = List.map (fun scope -> List.map (fun (sym, value) -> sym ^ " -> " ^ value_to_string value) scope) mem in
  String.concat "Scope\n" (List.map (String.concat ", ") mem_str)
  
and value_to_string (value: value): string =
  match value with
  | Ivalue n -> string_of_int n
  | Rvalue f -> string_of_float f
  | Error s -> "Error: " ^ s

and statement_to_string (s: ast_s): string =
  match s with
  | AST_i_dec (id, vloc) -> "AST_i_dec: " ^ id
  | AST_r_dec (id, vloc) -> "AST_r_dec: " ^ id
  | AST_read (id, loc) -> "AST_read: " ^ id
  | AST_write (expr) -> "AST_write"
  | AST_assign (id, expr, vloc, aloc) -> "AST_assign: " ^ id
  | AST_if (cond, sl) -> "AST_if"
  | AST_do (sl) -> "AST_do"
  | AST_check (cond, cloc) -> "AST_check"
  | AST_error -> "AST_error"

(* NB: the following routine is complete.  You can call it on any
   statement node and it will figure out what more specific case to invoke. *)
and interpret_s (loop_count:int) (iter1:bool) (s:ast_s) (mem:memory)
                (inp:string list) (outp:string list)
    : status * memory * string list * string list =
    (*  ok?    new_mem  new_input     new_output *)
  match s with
  | AST_i_dec(id, vloc)  -> interpret_dec iter1 id (Ivalue(0)) vloc mem inp outp
  | AST_r_dec(id, vloc)  -> interpret_dec iter1 id (Rvalue(0.0)) vloc mem inp outp
  | AST_read(id, loc)                -> interpret_read id loc mem inp outp
  | AST_write(expr)                  -> interpret_write expr mem inp outp
  | AST_assign(id, expr, vloc, aloc) -> interpret_assign id expr vloc aloc mem inp outp
  | AST_if(cond, sl)                 -> interpret_if loop_count cond sl mem inp outp
  | AST_do(sl)                       -> interpret_do loop_count true sl mem inp outp
  | AST_check(cond, cloc)            -> if loop_count > 0
                                          then interpret_check cond mem inp outp
                                          else (Bad, [], [], outp @
                                            [complaint cloc "check not inside a loop"])
  | AST_error                        -> raise (Failure "cannot interpret erroneous tree")

(* Check for errors:
   1. Redeclaration of variable in same scope (as long as iter1 = true)
*)
and interpret_dec (iter1:bool) (id:string) (v:value) (vloc:row_col)
                  (mem:memory) (inp:string list) (outp:string list)
    : status * memory * string list * string list =
    (*  ok?    new_mem  new_input     new_output *)
  (*
    1. check if variable exists
    2. if it does: complain that variable is already defined
    3. if not: insert_mem with placeholder 0 or 0.0, return (Good, new_mem, inp, outp)
  *)
    match iter1 with
    | true -> 
        let new_mem, var_did_insert = insert_mem id v mem in 
        if var_did_insert then
          (Good, new_mem, inp, outp)
        else
          (Bad, [], [], outp @ [complaint vloc "Variable " ^ id ^ " is already defined in this scope"])
    | false -> (Good, mem, inp, outp)

(* Check for errors:
   1. Non-numeric input
   2. Unexpected end of input
   3. int id in mem, read id -> 2.0
   4. real id in mem, read id -> 2
   5. reading an undeclared variable: read n (when n is undeclared)
*)
and interpret_read (id:string) (loc:row_col) (mem:memory)
                   (inp:string list) (outp:string list)
    : status * memory * string list * string list =
    (*  ok?    new_mem  new_input     new_output *)
  
  let old_v = lookup_mem id loc mem in
  match inp with
  | [] -> (Bad, [], [], outp @ [complaint loc "unexpected end of input"])
  | str :: rest ->
      if String.contains str '.'
        then
          (* float case *)
          (match old_v with
          | Error(s) -> (Bad, [], [], outp @ [s])
          | Rvalue(_) -> 
              let string_to_float_safe str = 
                try 
                  Some (float_of_string str)
                with 
                | Failure _ -> None
              in
              (match string_to_float_safe str with
              | Some value -> 
                let new_mem = update_mem id (Rvalue(value)) mem in
                (Good, new_mem, rest, outp)
              | None -> (Bad, [], [], outp @ [complaint loc "Non-numeric input to variable " ^ id ^ " of type real"]))
          | Ivalue(_) -> (Bad, [], [], outp @ [complaint loc "Invalid input type to variable " ^ id ^ " of type int"]))
        else
          (* int case *)
          (match old_v with
            | Error(s) -> (Bad, [], [], outp @ [s])
            | Ivalue(_) -> 
                let string_to_int_safe str = 
                  try 
                    Some (int_of_string str)
                  with 
                  | Failure _ -> None
                in
                (match string_to_int_safe str with
                | Some value -> 
                  let new_mem = update_mem id (Ivalue(value)) mem in
                  (Good, new_mem, rest, outp)
                | None -> (Bad, [], [], outp @ [complaint loc "Non-numeric input to variable " ^ id ^ " of type int"]))
            | Rvalue(_) -> (Bad, [], [], outp @ [complaint loc "Invalid input type to variable " ^ id ^ " of type real"]))
                

(* NB: the following routine is complete. *)
and interpret_write (expr:ast_e) (mem:memory)
                    (inp:string list) (outp:string list)
    : status * memory * string list * string list =
    (*  ok?    new_mem  new_input     new_output *)
  let (ve, new_mem)  = interpret_expr expr mem in
    match ve with
    | Ivalue(n) -> (Good, new_mem, inp, outp @ [string_of_int n])
    | Rvalue(r) -> (Good, new_mem, inp, outp @ [string_of_float r])
    | Error(s)  -> (Bad, [], [], outp @ [s])

(* Check for errors:
   1. Use of undeclared variable (use old_v from lookup, check for Error)
   2. Type clash in assignment (use old_v for type check)
*)
and interpret_assign (lhs:string) (rhs:ast_e) (vloc:row_col) (aloc:row_col)
                     (mem:memory) (inp:string list) (outp:string list)
    : status * memory * string list * string list =
    (*  ok?    new_mem  new_input     new_output *)
  match lookup_mem lhs vloc mem with
  | Error(s) -> (Bad, [], [], outp @ [s])
  | old_v ->
      let (v, m) = interpret_expr rhs mem in
      (match old_v with
      | Ivalue(_) -> 
        (match v with
        | Ivalue(_) -> 
          let new_mem = update_mem lhs v m in
          (Good, new_mem, inp, outp)
        | Rvalue(_) -> (Bad, [], [], outp @ [complaint aloc "unexpected value type, needed int"])
        | Error(s) -> (Bad, [], [], outp @ [s]))
      | Rvalue(_) ->
        (match v with
        | Rvalue(_) ->
          let new_mem = update_mem lhs v m in
          (Good, new_mem, inp, outp)
        | Ivalue(_) -> (Bad, [], [], outp @ [complaint aloc "unexpected value type, needed real"])
        | Error(s) -> (Bad, [], [], outp @ [s]))
      )

and interpret_if (loop_count:int) (cond:ast_c) (sl:ast_sl) (mem:memory)
                 (inp:string list) (outp:string list)
    : status * memory * string list * string list =
    (*  ok?    new_mem  new_input     new_output *)
  let (op, e1, e2, op_loc) = cond in
  let (v, m) = interpret_cond (op, e1, e2, op_loc) mem in
  match v with
  | Ivalue(1) -> 
    let scope = new_scope m in
    let (new_status, new_mem, new_inp, new_outp) = interpret_sl loop_count true sl scope inp outp in
    (new_status, (end_scope new_mem), new_inp, new_outp)
  | Ivalue(0) -> (Good, m, inp, outp)
  | Error (s) -> (Bad, [], [], outp @ [s])

and interpret_do (loop_count:int) (iter1:bool) (sl:ast_sl) (mem:memory)
                 (inp:string list) (outp:string list)
    : status * memory * string list * string list =
    (*  ok?    new_mem  new_input     new_output *)

  (* first run *)
  let mem_pushed = if iter1 then (new_scope mem) else mem in
  let (status, new_mem, new_inp, new_outp) = interpret_sl (loop_count+1) iter1 sl mem_pushed inp outp in
  
  match status with
  | Good -> (* Finished first run successfully *)
  interpret_do (loop_count+1) false sl new_mem new_inp new_outp
  | Done -> 
    (Good, end_scope new_mem, new_inp, new_outp)
  | Bad -> (Bad, new_mem, new_inp, new_outp)

  

and interpret_check (cond:ast_c) (mem:memory)
                    (inp:string list) (outp:string list)
    : status * memory * string list * string list =
    (*  ok?    new_mem  new_input     new_output *)
    let (op, e1, e2, op_loc) = cond in
    let (v, m) = interpret_cond (op, e1, e2, op_loc) mem in
    match v with
      | Ivalue(1) -> (Good, m, inp, outp)
      | Ivalue(0) -> (Done, m, inp, outp)
      | Error (s) -> (Bad, [], [], outp @ [s])


(* Check for errors:
   1. Type clash in binary expression: 2 + 2.0 
   2. Division by zero
   3. Non-real to trunc: trunc(real)
   4. Non-int to float: float(int)
   5. Use of undeclared variable (x + 2, when x is undeclared)
*)
and interpret_expr (expr:ast_e) (mem:memory) : value * memory =
    match expr with
    | AST_int (num, loc) -> (Ivalue(int_of_string num), mem)
    | AST_real (num, loc) -> (Rvalue(float_of_string num), mem)
    | AST_id (id, loc) -> (lookup_mem id loc mem, mem)
    | AST_trunc (inner_expr, loc) -> 
      let (v, m) = interpret_expr inner_expr mem in
      (match v with 
      | Rvalue(r) -> (Ivalue(int_of_float r), m)
      | Ivalue(_) -> (Error (complaint loc "Expected real inside trunc"), mem)
      | Error(s) -> (Error(s), mem))
    | AST_float (inner_expr, loc) -> 
      let (v, m) = interpret_expr inner_expr mem in
      (match v with 
      | Ivalue(i) -> (Rvalue(float_of_int i), m)
      | Rvalue(_) -> (Error (complaint loc "Expected int inside float"), mem)
      | Error(s) -> (Error(s), mem))
    | AST_binop (op, e1, e2, op_loc) -> 
      let (v1, m1) = interpret_expr e1 mem in
      let (v2, m2) = interpret_expr e2 m1 in
      (match v1 with
      | Ivalue(i1) ->
        (match v2 with
        | Ivalue(i2) -> 
          (match op with
          | "+" -> (Ivalue(i1 + i2), m2)
          | "-" -> (Ivalue(i1 - i2), m2)
          | "*" -> (Ivalue(i1 * i2), m2)
          | "/" ->
            if i2 = 0 then (Error (complaint op_loc "Second operand is 0 during division"), m2)
            else (Ivalue(i1 / i2), m2)
          | _ -> (Error(complaint op_loc "Invalid operator"), m2))
        | Rvalue(_) -> (Error (complaint op_loc "Second operand of ao/mo is not int"), m2)
        | Error(s) -> (Error(s), m2))
      | Rvalue(r1) ->
        (match v2 with
        | Rvalue(r2) -> 
          (match op with
          | "+" -> (Rvalue(r1 +. r2), m2)
          | "-" -> (Rvalue(r1 -. r2), m2)
          | "*" -> (Rvalue(r1 *. r2), m2)
          | "/" ->
            if r2 = 0. then (Error (complaint op_loc "Second operand is 0 during division"), m2)
            else (Rvalue(r1 /. r2), m2)
          | _ -> (Error(complaint op_loc "Invalid operator"), m2))
        | Ivalue(_) -> (Error (complaint op_loc "Second operand of ao/mo is not real"), m2)
        | Error(s) -> (Error(s), m2))
      | Error(s) -> (Error(s), m2))

(* Type clash in comparison: 2 < 3.2 *)
and interpret_cond ((op:string), (lo:ast_e), (ro:ast_e), (loc:row_col)) (mem:memory)
    : value * memory =
    let (v1, m1) = interpret_expr lo mem in
    let (v2, m2) = interpret_expr ro m1 in
    match v1 with
      | Ivalue(i1) ->
        (match v2 with
        | Ivalue(i2) -> 
          (match op with
          | "==" -> 
            if i1 = i2 then (Ivalue(1), m2) 
            else (Ivalue(0), m2)
          | "!=" -> 
            if i1 <> i2 then (Ivalue(1), m2) 
            else (Ivalue(0), m2)
          | ">" -> 
            if i1 > i2 then (Ivalue(1), m2) 
            else (Ivalue(0), m2)
          | "<" -> 
            if i1 < i2 then (Ivalue(1), m2) 
            else (Ivalue(0), m2)
          | ">=" -> 
            if i1 >= i2 then (Ivalue(1), m2) 
            else (Ivalue(0), m2)
          | "<=" -> 
            if i1 <= i2 then (Ivalue(1), m2) 
            else (Ivalue(0), m2)
          | _ -> (Error(complaint loc "Invalid operator"), m2))
        | Rvalue(_) -> (Error (complaint loc "Second operand of comparison is not int"), m2)
        | Error(s) -> (Error(s), m2))
      | Rvalue(r1) ->
        (match v2 with
        | Rvalue(r2) -> 
          (match op with
          | "==" -> 
            if r1 = r2 then (Ivalue(1), m2) 
            else (Ivalue(0), m2)
          | "!=" -> 
            if r1 <> r2 then (Ivalue(1), m2) 
            else (Ivalue(0), m2)
          | ">" -> 
            if r1 > r2 then (Ivalue(1), m2) 
            else (Ivalue(0), m2)
          | "<" -> 
            if r1 < r2 then (Ivalue(1), m2) 
            else (Ivalue(0), m2)
          | ">=" -> 
            if r1 >= r2 then (Ivalue(1), m2) 
            else (Ivalue(0), m2)
          | "<=" -> 
            if r1 <= r2 then (Ivalue(1), m2) 
            else (Ivalue(0), m2)
          | _ -> (Error(complaint loc "Invalid operator"), m2))
        | Ivalue(_) -> (Error (complaint loc "Second operand of comparison is not real"), m2)
        | Error(s) -> (Error(s), m2))
      | Error(s) -> (Error(s), m2)

(*******************************************************************
    Testing
 *******************************************************************)

let sum_ave_prog =
"   read int a read int b int sum := a + b
    write sum write float(sum) / 2.0";;

let primes_prog =
"   read int n
    int cp := 2
    do 
        check n > 0
        int found := 0
        int cf1 := 2
        int cf1s := cf1 * cf1
        do
            check cf1s <= cp
            int cf2 := 2
            int pr := cf1 * cf2
            do
                check pr <= cp
                if pr == cp
                    found := 1
                fi
                cf2 := cf2 + 1
                pr := cf1 * cf2
            od
            cf1 := cf1 + 1
            cf1s := cf1 * cf1
        od
        if found == 0
            write cp
            n := n - 1
        fi
        cp := cp + 1
    od";;

let gcd_prog =
"   read int a
    read int b
    do 
        check a != b
        if a > b
            a := a - b
        fi
        if b > a
            b := b - a
        fi
        if a == b
            write a
        fi
    od";;

let sqrt_prog =
"   read real d
    real l := d / 2.0
    do
        check l * l > d
        l := l / 2.0
    od
    real h := 2.0 * l
    real err := d - (l * l)
    if err < 0.0 err := 0.0 - err fi
    do
        check err > 1.e-10
        real a := (l + h) / 2.0
        if (a * a) < d l := a fi
        if (a * a) > d h := a fi
        err := d - (l * l)
        if err < 0.0 err := 0.0 - err fi
    od
    write l";;

let ecg_ast prog =
  ast_ize_prog (parse ecg_parse_table prog);;

let ecg_run prog inp =
  interpret (ecg_ast prog) inp;;

let sum_ave_parse_tree = parse ecg_parse_table sum_ave_prog;;
let sum_ave_syntax_tree = ast_ize_prog sum_ave_parse_tree;;

let primes_parse_tree = parse ecg_parse_table primes_prog;;
let primes_syntax_tree = ast_ize_prog primes_parse_tree;;

let gcd_parse_tree = parse ecg_parse_table gcd_prog;;
let gcd_syntax_tree = ast_ize_prog gcd_parse_tree;;

let show_ast prog = pp_p (ast_ize_prog (parse ecg_parse_table prog));;

let main () =

  (*
  print_string (interpret sum_ave_syntax_tree "4 6");
    (* should print "10 5" *)
  print_newline ();
  print_string (interpret primes_syntax_tree "10");
    (* should print "2 3 5 7 11 13 17 19 23 29" *)
  print_newline ();
  print_string (interpret sum_ave_syntax_tree "4 foo");
    (* should print " line 2, col 25: non-numeric input" *)
  print_newline ();
  print_string (ecg_run "write 3 write 2 / 0" "");
    (* should print "3  line1, col 17: divide by zero" *)
  print_newline ();
  print_string (ecg_run "write foo" "");
    (* should print " line 1, col 7: foo not found" *)
  print_newline ();
  print_string (ecg_run "read int a read int b" "3");
    (* should print " line 1, col 21: unexpected end of input" *)
  print_newline ();
  *)


(* Code below expects there to be a single command-line argument, which
   names a file containing an ecg program.  It runs that program, taking
   input from stdin.  It does NOT run interactively: it sucks up _all_
   input and runs only once it reaches end-of-file. *)

  let read_prog () =
    if Array.length Sys.argv != 2
      then raise (Failure ("usage: " ^ Sys.argv.(0) ^ " prog_file_name"))
      else
        let ic = open_in Sys.argv.(1) in
        let lines = ref [] in
        try
          while true do
            lines := input_line ic :: !lines;
          done; ""
        with
          End_of_file ->
            String.concat "\n" (rev !lines) in

  let read_input () =
    let lines = ref [] in
      try
        while true do
          lines := read_line () :: !lines;
        done; ""
      with
        End_of_file ->
          String.concat "\n" (rev !lines) in

  let prog = read_prog() in
  let input = read_input() in
  print_string (ecg_run prog input);;

(* Execute function "main" iff run as a stand-alone program. *)
if !Sys.interactive then () else main ();;
