
type __ = Obj.t

val add : int -> int -> int

val sub : int -> int -> int

val eqb : int -> int -> bool

val leb : int -> int -> bool

val ltb : int -> int -> bool

type reflect =
| ReflectT
| ReflectF

val last : 'a1 list -> 'a1 -> 'a1

val reflect_intro : bool -> reflect

val pr1 : ('a1 * 'a2) -> 'a1

val pr2 : ('a1 * 'a2) -> 'a2

val putin : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list

val sort : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list

module Decidable :
 sig
  type coq_type = { eqb : (__ -> __ -> bool); eqP : (__ -> __ -> reflect) }

  type coq_E = __

  val eqb : coq_type -> coq_E -> coq_E -> bool
 end

val nat_eqP : int -> int -> reflect

val nat_eqType : Decidable.coq_type

type bid = { bp : int; btime : int; bq : int; idb : int }

val b_eqb : bid -> bid -> bool

type ask = { sp : int; stime : int; sq : int; ida : int }

val a_eqb : ask -> ask -> bool

type fill_type = { bid_of : bid; ask_of : ask; tq : int; tp : int }

val b0 : bid

val a0 : ask

val m0 : fill_type

val ttqb : fill_type list -> bid -> int

val ttqa : fill_type list -> ask -> int

val by_dbp : bid -> bid -> bool

val m_dbp : fill_type -> fill_type -> bool

val fOB_aux : fill_type list -> bid list -> int -> fill_type list

val fOB : fill_type list -> bid list -> fill_type list

val by_sp : ask -> ask -> bool

val m_sp : fill_type -> fill_type -> bool

val fOA_aux : fill_type list -> ask list -> int -> fill_type list

val fOA : fill_type list -> ask list -> fill_type list

val uM_aux : bid list -> ask list -> int -> int -> fill_type list

val replace_column : fill_type list -> int -> fill_type list

val uniform_price : bid list -> ask list -> int

val mM_aux : bid list -> ask list -> int -> int -> fill_type list

val by_dsp : ask -> ask -> bool

val fAIR : fill_type list -> bid list -> ask list -> fill_type list

val uM : bid list -> ask list -> fill_type list

val mM : bid list -> ask list -> fill_type list
