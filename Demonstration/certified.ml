
type __ = Obj.t

(** val add : int -> int -> int **)

let rec add = ( + )

(** val sub : int -> int -> int **)

let rec sub n m =
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ -> n)
    (fun k ->
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> n)
      (fun l -> sub k l)
      m)
    n

(** val eqb : int -> int -> bool **)

let rec eqb = ( = )

(** val leb : int -> int -> bool **)

let rec leb = (<=)

(** val ltb : int -> int -> bool **)

let ltb n m =
  leb ((fun x -> x + 1) n) m

type reflect =
| ReflectT
| ReflectF

(** val last : 'a1 list -> 'a1 -> 'a1 **)

let rec last l d =
  match l with
  | [] -> d
  | a :: l0 -> (match l0 with
                | [] -> a
                | _ :: _ -> last l0 d)

(** val reflect_intro : bool -> reflect **)

let reflect_intro = function
| true -> ReflectT
| false -> ReflectF

(** val pr1 : ('a1 * 'a2) -> 'a1 **)

let pr1 = function
| pr3,_ -> pr3

(** val pr2 : ('a1 * 'a2) -> 'a2 **)

let pr2 = function
| _,pr3 -> pr3

(** val putin : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list **)

let rec putin lr a l = match l with
| [] -> a :: []
| b :: l1 -> if lr a b then a :: l else b :: (putin lr a l1)

(** val sort : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec sort lr = function
| [] -> []
| a :: l1 -> putin lr a (sort lr l1)

module Decidable =
 struct
  type coq_type = { eqb : (__ -> __ -> bool); eqP : (__ -> __ -> reflect) }

  type coq_E = __

  (** val eqb : coq_type -> coq_E -> coq_E -> bool **)

  let eqb t =
    t.eqb
 end

(** val nat_eqP : int -> int -> reflect **)

let nat_eqP x y =
  reflect_intro (eqb x y)

(** val nat_eqType : Decidable.coq_type **)

let nat_eqType =
  { Decidable.eqb = (Obj.magic eqb); Decidable.eqP = (Obj.magic nat_eqP) }

type bid = { bp : int; btime : int; bq : int; idb : int }

(** val b_eqb : bid -> bid -> bool **)

let b_eqb x y =
  (&&)
    ((&&)
      ((&&) (nat_eqType.Decidable.eqb (Obj.magic x.idb) (Obj.magic y.idb))
        (nat_eqType.Decidable.eqb (Obj.magic x.btime) (Obj.magic y.btime)))
      (nat_eqType.Decidable.eqb (Obj.magic x.bq) (Obj.magic y.bq)))
    (nat_eqType.Decidable.eqb (Obj.magic x.bp) (Obj.magic y.bp))

type ask = { sp : int; stime : int; sq : int; ida : int }

(** val a_eqb : ask -> ask -> bool **)

let a_eqb x y =
  (&&)
    ((&&)
      ((&&) (nat_eqType.Decidable.eqb (Obj.magic x.ida) (Obj.magic y.ida))
        (nat_eqType.Decidable.eqb (Obj.magic x.stime) (Obj.magic y.stime)))
      (nat_eqType.Decidable.eqb (Obj.magic x.sq) (Obj.magic y.sq)))
    (nat_eqType.Decidable.eqb (Obj.magic x.sp) (Obj.magic y.sp))

type fill_type = { bid_of : bid; ask_of : ask; tq : int; tp : int }

(** val b0 : bid **)

let b0 =
  { bp = 0; btime = 0; bq = 0; idb = 0 }

(** val a0 : ask **)

let a0 =
  { sp = 0; stime = 0; sq = 0; ida = 0 }

(** val m0 : fill_type **)

let m0 =
  { bid_of = b0; ask_of = a0; tq = 0; tp = 0 }

(** val ttqb : fill_type list -> bid -> int **)

let rec ttqb f b =
  match f with
  | [] -> 0
  | f0 :: f' -> if b_eqb b f0.bid_of then add f0.tq (ttqb f' b) else ttqb f' b

(** val ttqa : fill_type list -> ask -> int **)

let rec ttqa f a =
  match f with
  | [] -> 0
  | f0 :: f' -> if a_eqb a f0.ask_of then add f0.tq (ttqa f' a) else ttqa f' a

(** val by_dbp : bid -> bid -> bool **)

let by_dbp b1 b2 =
  (||) (ltb b2.bp b1.bp) ((&&) (eqb b2.bp b1.bp) (leb b1.btime b2.btime))

(** val m_dbp : fill_type -> fill_type -> bool **)

let m_dbp m1 m2 =
  by_dbp m1.bid_of m2.bid_of

(** val fOB_aux : fill_type list -> bid list -> int -> fill_type list **)

let fOB_aux a a1 b =
  let rec fix_F x =
    let t = pr2 (pr2 x) in
    (match pr1 x with
     | [] -> []
     | f :: l ->
       (match pr1 (pr2 x) with
        | [] -> []
        | b1 :: l0 ->
          if eqb f.tq (sub b1.bq t)
          then { bid_of = b1; ask_of = f.ask_of; tq = (sub b1.bq t); tp =
                 f.tp } :: (let y = l,(l0,0) in fix_F y)
          else if leb f.tq (sub b1.bq t)
               then { bid_of = b1; ask_of = f.ask_of; tq = f.tq; tp =
                      f.tp } :: (let y = l,((b1 :: l0),(add t f.tq)) in
                                 fix_F y)
               else { bid_of = b1; ask_of = f.ask_of; tq = (sub b1.bq t);
                      tp =
                      f.tp } :: (let y = ({ bid_of = f.bid_of; ask_of =
                                   f.ask_of; tq = (sub f.tq (sub b1.bq t));
                                   tp = f.tp } :: l),(l0,0)
                                 in
                                 fix_F y)))
  in fix_F (a,(a1,b))

(** val fOB : fill_type list -> bid list -> fill_type list **)

let fOB m b =
  fOB_aux m b 0

(** val by_sp : ask -> ask -> bool **)

let by_sp s1 s2 =
  (||) (ltb s1.sp s2.sp) ((&&) (eqb s1.sp s2.sp) (leb s1.stime s2.stime))

(** val m_sp : fill_type -> fill_type -> bool **)

let m_sp m1 m2 =
  by_sp m1.ask_of m2.ask_of

(** val fOA_aux : fill_type list -> ask list -> int -> fill_type list **)

let fOA_aux a a1 b =
  let rec fix_F x =
    let t = pr2 (pr2 x) in
    (match pr1 x with
     | [] -> []
     | f :: l ->
       (match pr1 (pr2 x) with
        | [] -> []
        | a2 :: l0 ->
          if eqb f.tq (sub a2.sq t)
          then { bid_of = f.bid_of; ask_of = a2; tq = (sub a2.sq t); tp =
                 f.tp } :: (let y = l,(l0,0) in fix_F y)
          else if leb f.tq (sub a2.sq t)
               then { bid_of = f.bid_of; ask_of = a2; tq = f.tq; tp =
                      f.tp } :: (let y = l,((a2 :: l0),(add t f.tq)) in
                                 fix_F y)
               else { bid_of = f.bid_of; ask_of = a2; tq = (sub a2.sq t);
                      tp =
                      f.tp } :: (let y = ({ bid_of = f.bid_of; ask_of =
                                   f.ask_of; tq = (sub f.tq (sub a2.sq t));
                                   tp = f.tp } :: l),(l0,0)
                                 in
                                 fix_F y)))
  in fix_F (a,(a1,b))

(** val fOA : fill_type list -> ask list -> fill_type list **)

let fOA m a =
  fOA_aux m a 0

(** val fAIR : fill_type list -> bid list -> ask list -> fill_type list **)

let fAIR m b a =
  fOB (sort m_dbp (fOA (sort m_sp m) (sort by_sp a))) (sort by_dbp b)

(** val uM_aux : bid list -> ask list -> int -> int -> fill_type list **)

let uM_aux a a1 a2 b =
  let rec fix_F x =
    let tb = pr1 (pr2 (pr2 x)) in
    let ta = pr2 (pr2 (pr2 x)) in
    (match pr1 x with
     | [] -> []
     | b1 :: l ->
       (match pr1 (pr2 x) with
        | [] -> []
        | a3 :: l0 ->
          if leb a3.sp b1.bp
          then if eqb (sub b1.bq tb) (sub a3.sq ta)
               then { bid_of = b1; ask_of = a3; tq = (sub b1.bq tb); tp =
                      b1.bp } :: (let y = l,(l0,(0,0)) in fix_F y)
               else if leb (sub b1.bq tb) (sub a3.sq ta)
                    then { bid_of = b1; ask_of = a3; tq = (sub b1.bq tb);
                           tp =
                           b1.bp } :: (let y =
                                         l,((a3 :: l0),(0,(add ta
                                                            (sub b1.bq tb))))
                                       in
                                       fix_F y)
                    else { bid_of = b1; ask_of = a3; tq = (sub a3.sq ta);
                           tp =
                           b1.bp } :: (let y =
                                         (b1 :: l),(l0,((add tb
                                                          (sub a3.sq ta)),0))
                                       in
                                       fix_F y)
          else []))
  in fix_F (a,(a1,(a2,b)))

(** val replace_column : fill_type list -> int -> fill_type list **)

let rec replace_column l n =
  match l with
  | [] -> []
  | m :: l' ->
    { bid_of = m.bid_of; ask_of = m.ask_of; tq = m.tq; tp =
      n } :: (replace_column l' n)

(** val uniform_price : bid list -> ask list -> int **)

let uniform_price b a =
  (last (uM_aux b a 0 0) m0).bid_of.bp

(** val uM : bid list -> ask list -> fill_type list **)

let uM b a =
  replace_column (uM_aux (sort by_dbp b) (sort by_sp a) 0 0)
    (uniform_price (sort by_dbp b) (sort by_sp a))

(** val mM_aux : bid list -> ask list -> int -> int -> fill_type list **)

let mM_aux a a1 a2 b =
  let rec fix_F x =
    let tb = pr1 (pr2 (pr2 x)) in
    let ta = pr2 (pr2 (pr2 x)) in
    (match pr1 x with
     | [] -> []
     | b1 :: l ->
       (match pr1 (pr2 x) with
        | [] -> []
        | a3 :: l0 ->
          if leb a3.sp b1.bp
          then if eqb (sub b1.bq tb) (sub a3.sq ta)
               then { bid_of = b1; ask_of = a3; tq = (sub b1.bq tb); tp =
                      b1.bp } :: (let y = l,(l0,(0,0)) in fix_F y)
               else if leb (sub b1.bq tb) (sub a3.sq ta)
                    then { bid_of = b1; ask_of = a3; tq = (sub b1.bq tb);
                           tp =
                           b1.bp } :: (let y =
                                         l,((a3 :: l0),(0,(add ta
                                                            (sub b1.bq tb))))
                                       in
                                       fix_F y)
                    else { bid_of = b1; ask_of = a3; tq = (sub a3.sq ta);
                           tp =
                           b1.bp } :: (let y =
                                         (b1 :: l),(l0,((add tb
                                                          (sub a3.sq ta)),0))
                                       in
                                       fix_F y)
          else let y = (b1 :: l),(l0,(tb,0)) in fix_F y))
  in fix_F (a,(a1,(a2,b)))

(** val by_dsp : ask -> ask -> bool **)

let by_dsp s1 s2 =
  (||) (ltb s2.sp s1.sp) ((&&) (eqb s2.sp s1.sp) (leb s2.stime s1.stime))

(** val mM : bid list -> ask list -> fill_type list **)

let mM b a =
  mM_aux (sort by_dbp b) (sort by_dsp a) 0 0
