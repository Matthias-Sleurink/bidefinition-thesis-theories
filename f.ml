structure test : sig
  type char
  type 'a set
  type ('a, 'b) sum
  type 'a bd
  val fail : 'a bd
  val parse : 'a bd -> char list -> ('a * char list) option
  val t : (char * char list) option
end = struct

fun equal_bool p true = p
  | equal_bool p false = not p
  | equal_bool true p = p
  | equal_bool false p = not p;

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

fun equal_chara (Chara (x1, x2, x3, x4, x5, x6, x7, x8))
  (Chara (y1, y2, y3, y4, y5, y6, y7, y8)) =
  equal_bool x1 y1 andalso
    (equal_bool x2 y2 andalso
      (equal_bool x3 y3 andalso
        (equal_bool x4 y4 andalso
          (equal_bool x5 y5 andalso
            (equal_bool x6 y6 andalso
              (equal_bool x7 y7 andalso equal_bool x8 y8))))));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_char = {equal = equal_chara} : char equal;

datatype 'a set = Set of 'a list | Coset of 'a list;

datatype ('a, 'b) sum = Inl of 'a | Inr of 'b;

datatype 'a bd =
  Abs_bd of
    (((char list), 'a) sum -> (('a * char list), (char list)) sum option);

fun id x = (fn xa => xa) x;

fun eq A_ a b = equal A_ a b;

val bot_set : 'a set = Set [];

fun one_char_printer c = SOME [c];

fun one_char_parser [] = NONE
  | one_char_parser (c :: cs) = SOME (c, cs);

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

fun bdc_aux parser printer (Inl s) = map_option Inl (parser s)
  | bdc_aux parser printer (Inr t) = map_option Inr (printer t);

fun bdc xb xc = Abs_bd (bdc_aux xb xc);

val one_char : char bd = bdc one_char_parser one_char_printer;

fun return A_ t =
  bdc (fn i => SOME (t, i)) (fn ta => (if eq A_ ta t then SOME [] else NONE));

val fail : 'a bd = bdc (fn _ => NONE) (fn _ => NONE);

fun projl (Inl x1) = x1;

fun pr_map f (pr, pl) = (f pr, pl);

fun opr_map f NONE = NONE
  | opr_map f (SOME p) = SOME (pr_map f p);

fun projr (Inr x2) = x2;

fun print_aux bd_aux s = map_option projr (bd_aux (Inr s));

fun rep_bd (Abs_bd x) = x;

fun print xa = print_aux (rep_bd xa);

fun parse_aux bd_aux s = map_option projl (bd_aux (Inl s));

fun parse xa = parse_aux (rep_bd xa);

fun transform a2b b2a bd = bdc (opr_map a2b o parse bd) (print bd o b2a);

fun binda NONE f = NONE
  | binda (SOME x) f = f x;

fun ite_printer pa a2pb pc b2a (Inl b) =
  let
    val a = b2a b;
  in
    binda (pa a) (fn pra => binda (a2pb a b) (fn prb => SOME (pra @ prb)))
  end
  | ite_printer pa a2pb pc b2a (Inr c) = pc c;

fun ite_parser a a2b c i =
  (case a i of NONE => opr_map Inr (c i)
    | SOME (r, l) => opr_map Inl (a2b r l));

fun ite a a2b c b2a =
  bdc (ite_parser (parse a) (parse o a2b) (parse c))
    (ite_printer (print a) (print o a2b) (print c) b2a);

fun bind a a2bd b2a = transform projl Inl (ite a a2bd fail b2a);

fun char_if p =
  bind one_char (fn r => (if p r then return equal_char r else fail)) id;

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun member A_ x (Coset xs) = not (membera A_ xs x)
  | member A_ x (Set xs) = membera A_ xs x;

fun in_set s = char_if (fn i => member equal_char i s);

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun insert A_ x (Coset xs) = Coset (removeAll A_ x xs)
  | insert A_ x (Set xs) = Set (inserta A_ x xs);

val t : (char * char list) option =
  parse (in_set
          (insert equal_char
            (Chara (true, false, false, false, false, true, true, false))
            bot_set))
    [Chara (true, false, false, false, false, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (false, false, true, true, false, true, true, false),
      Chara (true, false, true, false, false, true, true, false)];

end; (*struct test*)
