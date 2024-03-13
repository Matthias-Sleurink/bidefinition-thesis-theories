structure test : sig
  type 'a enum
  val t : 'c enum -> ('a -> 'b -> bool) -> ('c -> 'a) -> ('c -> 'b) -> bool
end = struct

type 'a finite = {};

type 'a enum =
  {finite_enum : 'a finite, enum : 'a list, enum_all : ('a -> bool) -> bool,
    enum_ex : ('a -> bool) -> bool};
val finite_enum = #finite_enum : 'a enum -> 'a finite;
val enum = #enum : 'a enum -> 'a list;
val enum_all = #enum_all : 'a enum -> ('a -> bool) -> bool;
val enum_ex = #enum_ex : 'a enum -> ('a -> bool) -> bool;

fun all A_ p = enum_all A_ p;

fun fun_ord C_ ord f g = all C_ (fn x => ord (f x) (g x));

fun t C_ = fun_ord C_;

end; (*struct test*)
