open List

let runtests = true

module SMap = struct
  include Map.Make(String)
end

module SSet = struct
  include Set.Make(String)
end

(* proposition formula *)
type pf =
  | True
  | False
  | Var of string
  | Not of pf
  | And of pf * pf
  | Or of pf * pf
  | Imp of pf * pf
  | Iff of pf * pf

let rec disjuncts = function
  | Or (f1, f2) -> disjuncts f1 @ disjuncts f2
  | f -> [f]

let rec conjuncts = function
  | And (f1, f2) -> conjuncts f1 @ conjuncts f2
  | f -> [f]

module Fmt = struct
  open Format

  let rec list pp fmt = function
    | [] -> ()
    | [x] -> pp fmt x
    | x :: xs -> fprintf fmt "%a@ %a" pp x (list pp) xs

  let rec pf fmt =
    let open Format in
    function
    | True -> pp_print_string fmt "true"
    | False -> pp_print_string fmt "false"
    | Var v -> pp_print_string fmt v
    | Not f -> fprintf fmt "(not %a)" pf f
    | And _ as f -> fprintf fmt "@[<h>(and@ @[<hov>%a@])@]" (list pf) (conjuncts f)
    | Or _ as f -> fprintf fmt "@[<h>(or@ @[<hov>%a@])@]" (list pf) (disjuncts f)
    | Imp (f1, f2) -> fprintf fmt "@[<hov2>(imp@ %a@ %a)@]" pf f1 pf f2
    | Iff (f1, f2) -> fprintf fmt "@[<hov2>(iff@ %a@ %a)@]" pf f1 pf f2
end

let mk_not f =
  match f with
  | True -> False
  | False -> True
  | Not f -> f
  | _ -> Not f

let mk_and f1 f2 =
  match f1, f2 with
  | True, f | f, True -> f
  | False, _ | _, False -> False
  | _ -> And (f1, f2)

let mk_or f1 f2 =
  match f1, f2 with
  | True, _ | _, True -> True
  | False, f | f, False -> f
  | _ -> Or (f1, f2)

let mk_imp f1 f2 =
  match f1, f2 with
  | _, True | False, _ -> True
  | True, f -> f
  | f, False -> Not f
  | _ -> Imp (f1, f2)

let mk_iff f1 f2 =
  match f1, f2 with
  | True, f | f, True -> f
  | False, f | f, False -> Not f
  | _ -> Iff (f1, f2)

let list_or = fold_left mk_or False

let list_and = fold_left mk_and True

let pfmap m = function
  | (True | False | Var _) as f -> f
  | Not f -> Not (m f)
  | And (f1, f2) -> And (m f1, m f2)
  | Or (f1, f2) -> Or (m f1, m f2)
  | Imp (f1, f2) -> Imp (m f1, m f2)
  | Iff (f1, f2) -> Iff (m f1, m f2)

(* remove true/false literals in a connective *)
let rmlit1 = function
  | (True | False | Var _) as f -> f
  | Not f -> mk_not f
  | And (f1, f2) -> mk_and f1 f2
  | Or (f1, f2) -> mk_or f1 f2
  | Imp (f1, f2) -> mk_imp f1 f2
  | Iff (f1, f2) -> mk_iff f1 f2

(* recursively remove all nested literals *)
let rec rmlit f = rmlit1 (pfmap rmlit f)

(* evaluate a formula in an assignment *)
let rec eval asn = function
  | True -> true
  | False -> false
  | Var v -> SMap.find v asn
  | Not f -> not (eval asn f)
  | And (f1, f2) -> eval asn f1 && eval asn f2
  | Or (f1, f2) -> eval asn f1 || eval asn f2
  | Imp (f1, f2) -> not (eval asn f1) || eval asn f2
  | Iff (f1, f2) -> eval asn f1 = eval asn f2

let rec vars = function
  | Var v -> SSet.singleton v
  | f ->
    let res = ref SSet.empty in
    ignore (pfmap (fun x -> res := SSet.union !res (vars x); x) f);
    !res

(* recursive sat algorithm *)
let sat f =
  let rec sat vs asn =
    try
      let v = SSet.choose vs in
      let vs' = SSet.remove v vs in
      sat vs' (SMap.add v true asn) || sat vs' (SMap.add v false asn)
    with Not_found ->
      eval asn f
  in
  sat (vars f) SMap.empty

(* tauto f = true IFF forall asn, eval asn (Not f) = false
                  IFF forall asn, eval asn f = true *)
let tauto f = not (sat (Not f))

(* assuming f is (A ? B), generate a formula equivalent
   to d <=> (A ? B) that is in cnf form if d, A, and B
   are atoms *)
let cnf_equiv d = function
  | True -> d
  | False -> Not d
  | Var _ as f -> And (Or (d, mk_not f), Or (mk_not d, f))
  | Not f -> And (Or (d, f), Or (mk_not d, mk_not f))
  | Or (f1, f2) ->
    And (Or (d, mk_not f1),
         And (Or (d, mk_not f2),
              Or (mk_not d, Or (f1, f2))))
  | And (f1, f2) ->
    And (Or (d, Or (mk_not f1, mk_not f2)),
         And (Or (mk_not d, f1),
              Or (mk_not d, f2)))
  | Imp (f1, f2) ->
    And (Or (d, f1),
         And (Or (d, mk_not f2),
              Or (mk_not d, Or (mk_not f1, f2))))
  | Iff (f1, f2) ->
    And (Or (d, Or (f1, f2)),
         And (Or (d, Or (mk_not f1, mk_not f2)),
              And (Or (mk_not d, Or (f1, mk_not f2)),
                   Or (mk_not d, Or (mk_not f1, f2)))))

let () = if runtests then begin
  (* some tests *)
  let a, b, c = Var "a", Var "b", Var "c" in
  assert (tauto (Iff (cnf_equiv a True, Iff (a, True))));
  assert (tauto (Iff (cnf_equiv a False, Iff (a, False))));
  assert (tauto (Iff (cnf_equiv a b, Iff (a, b))));
  assert (tauto (Iff (cnf_equiv a (Not b), Iff (a, Not b))));
  assert (tauto (Iff (cnf_equiv a (And (b, c)), Iff (a, And (b, c)))));
  assert (tauto (Iff (cnf_equiv a (Or (b, c)), Iff (a, Or (b, c)))));
  assert (tauto (Iff (cnf_equiv a (Imp (b, c)), Iff (a, Imp (b, c)))));
  assert (tauto (Iff (cnf_equiv a (Iff (b, c)), Iff (a, Iff (b, c)))));
  prerr_endline "cnf_equiv tests ok";
end

let mk_var n =
  n + 1, Var ("#_" ^ (string_of_int n))

(* returns the definitional cnf form *)
let rec defcnf n defs f =
  match f with
  | True | False | Var _ -> n, defs, f
  | Not f ->
    let n, defs, fa = defcnf n defs f in
    n, defs, mk_not fa
  | And (f1, f2) -> defop n defs mk_and f1 f2
  | Or (f1, f2) -> defop n defs mk_or f1 f2
  | Imp (f1, f2) -> defop n defs mk_imp f1 f2
  | Iff (f1, f2) -> defop n defs mk_iff f1 f2

and defop n defs mk f1 f2 =
  let n, defs, fa1 = defcnf n defs f1 in
  let n, defs, fa2 = defcnf n defs f2 in
  let n, fa = mk_var n in
  n, (cnf_equiv fa (mk fa1 fa2) :: defs), fa

let defcnf f =
  let _, defs, fa = defcnf 1 [] (rmlit f) in
  let clauses = concat (map conjuncts defs) in
  let non_trivial f =
    let disj = disjuncts f in
    not (exists (fun lit -> mem (mk_not lit) disj) disj)
  in
  let clauses = filter non_trivial clauses in
  fold_left mk_and fa clauses

let () = if runtests then begin
  let p, q, r, s = Var "p", Var "q", Var "r", Var "s" in
  let f = And (Or (p, And (q, Not r)), s) in
  Format.eprintf "%a@." Fmt.pf (defcnf f);
end

module Utils = struct
  let allsets k l =
    let ll = length l in
    if k > ll then invalid_arg "allsets";
    let rec loop f i j acc =
      if i < j
      then loop f (i + 1) j (f i acc)
      else acc
    in
    let rec go acc res j k =
      if k = 0 then (acc :: res) else
      loop (fun i res -> go (nth l i :: acc) res (i + 1) (k - 1))
        j (ll - k + 1) res
    in
    go [] [] 0 k

  let rec (--) i j = if i < j then i :: ((i + 1) -- j) else []

  let rec ( **) l1 l2 =
    match l1 with
    | [] -> []
    | x :: l1 -> rev_append (map (fun y -> (x,y)) l2) (l1 ** l2)

  let () = if runtests then begin
    let c36 = allsets 3 (1 -- 7) in
    assert (List.length (List.sort_uniq compare c36) = 20);
  end 

  let conjoin f l = list_and (map f l)
end

let print_dimacs file f =
  let vars, _ =
    SSet.fold (fun v (vars, n) ->
        (SMap.add v n vars, n+1))
      (vars f)
      (SMap.empty, 1)
  in
  let clauses = conjuncts f in
  Printf.fprintf file "p cnf %d %d\n"
    (SMap.cardinal vars) (List.length clauses);
  let print_lit = function
    | Not (Var v) -> Printf.fprintf file "-%d " (SMap.find v vars)
    | Var v -> Printf.fprintf file "%d " (SMap.find v vars)
    | _ -> invalid_arg "formula not in cnf"
  in
  List.iter (fun c ->
      List.iter print_lit (disjuncts c);
      Printf.fprintf file "0\n")
    clauses

module Ramsey = struct
  open Utils

  let gen s t n =
    let verts = 1 -- (n + 1) in
    let yesgrps = map (allsets 2) (allsets s verts) in
    let nogrps = map (allsets 2) (allsets t verts) in
    let e = function
      | [a;b] -> Var (Printf.sprintf "e_%d_%d" a b)
      | _ -> assert false
    in
    Or (list_or (map (fun l -> list_and @@ map e l) yesgrps),
        list_or (map (fun l -> list_and @@ map (fun x -> Not (e x)) l) nogrps))

  let () = if runtests then begin
    assert (not (tauto (gen 3 3 5)));
    assert (tauto (gen 3 3 6));
  end
end

module Pigeon = struct
  open Utils

  let gen k n =
    let holes = 1 -- (n + 1) in
    let things = 1 -- (k + 1) in
    let vin t h = Var (Printf.sprintf "in_%d_%d" t h) in
    let eachthinginahole = map (fun t -> list_or (map (vin t) holes)) things in
    let atmostonehole =
      map (fun t ->
            map (function [h1;h2] -> Not (And (vin t h1, vin t h2))
                        | _ -> assert false)
                (allsets 2 holes) |> list_and) things in
    let onethingperhole =
      map (fun h ->
            map (function [t1;t2] -> Not (And (vin t1 h, vin t2 h))
                        | _ -> assert false)
                (allsets 2 things) |> list_and) holes in
    list_and [
      list_and eachthinginahole;
      list_and atmostonehole;
      list_and onethingperhole
    ]

  let () = if runtests then begin
    let p22 = gen 2 2 in
    let p32 = gen 3 2 in
    let p44 = gen 4 4 in
    let p54 = gen 5 4 in
    Format.eprintf "pigeon 3 2: %a@." Fmt.pf p32;
    assert (sat p22);
    assert (not (sat p32));
    assert (sat p44);
    assert (not (sat p54));
  end
end

module Bitfns = struct
  open Utils

  (* full adder *)
  let fa x y z s c =
    let xor a b = Iff (a, Not b) in
    And (Iff (s, xor x (xor y z)),
         Iff (c, Or (And (x,y), Or (And (y,z), And (x,z)))))

  let shift n f m = f (n+m)

  let name s i = Var (s ^ "_" ^ string_of_int i)

  (* adder, n bits *)
  let ripplecarry n x y c out =
    conjoin (fun i -> fa (x i) (y i) (c i) (out i) (c (i+1))) (0 -- n)

  (* feed 0 as input carry *)
  let ripplecarry0 n x y c out =
    rmlit (ripplecarry n x y (fun i -> if i = 0 then False else c i) out)

  (* feed 1 as input carry *)
  let ripplecarry1 n x y c out =
    rmlit (ripplecarry n x y (fun i -> if i = 0 then True else c i) out)

  (* multiplex = {a if sel=0; b if sel=1} *)
  let mux sel a b =
    Or (And (Not sel, a), And (sel, b))

  (* adder on n bits, blocks of k bits in parallel
     x, y, (c 0)     the summands
     c0, c1, s0, s1  temporary storage
     (c (n+1))       the outgoing carry
     s               the sum
  *)
  let rec carryselect (n,k) x y c0 c1 s0 s1 c s =
    let k' = min n k in
    let fm =
      And (And (ripplecarry0 k' x y c0 s0, ripplecarry1 k' x y c1 s1),
           And (Iff (c k', mux (c 0) (c0 k') (c1 k')),
                conjoin (fun i -> Iff (s i, mux (c 0) (s0 i) (s1 i)))
                        (0 -- k)))
    in
    if n <= k' then fm else
    And (fm, carryselect
           (n-k, k) (shift k x) (shift k y) (shift k c0) (shift k c1)
           (shift k s0) (shift k s1) (shift k c) (shift k s))
end

module AdderEquiv = struct
  open Utils
  open Bitfns

  (* should produce only unsatisfiable formulas;
     it's amazing that this poses absolutely zero challenge to SAT
     solvers! *)
  let gen k n =
    let x, y, cs, cr, c0, c1, s0, s1, ss, sr =
      name "x", name "y", name "cs", name "cr", name "c0", name "c1",
      name "s0", name "s1", name "ss", name "sr"
    in
    And (
      list_and [
        ripplecarry n x y cr sr;
        carryselect (n,k) x y c0 c1 s0 s1 cs ss;
        Iff (cs 0, cr 0)
      ],
      Not (And (conjoin (fun i -> Iff (sr i, ss i)) (0 -- n),
                Iff (cs n, cr n)))
    )

  let () = if runtests then begin
    Format.eprintf "adder 1 2: %a@." Fmt.pf (gen 1 2);
    assert (not (sat (gen 1 1)));
    assert (not (sat (gen 2 2)));
  end
end

let () = if true then begin
  print_dimacs stdout (AdderEquiv.gen 10 128 |> defcnf)
end
