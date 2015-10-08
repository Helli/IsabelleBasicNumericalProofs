structure Test : sig
  type nibble
  type char
  val test : unit -> unit
end = struct

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

datatype nat = Nat of IntInf.int;

datatype num = One | Bit0 of num | Bit1 of num;

datatype nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 |
  Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD
  | NibbleE | NibbleF;

datatype char = Char of nibble * nibble;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun integer_of_nat (Nat x) = x;

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun equal_nat m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

val zero_nat : nat = Nat (0 : IntInf.int);

val one_nat : nat = Nat (1 : IntInf.int);

fun float_of n =
  (if equal_nat n zero_nat then 0.0
    else Real.+ (float_of (minus_nat n one_nat), 1.0));

val a : real = float_of (nat_of_integer (33 : IntInf.int));

val b : real =
  Real./ (float_of one_nat, float_of (nat_of_integer (1243313 : IntInf.int)));

val test_input : real * real = (a, b);

fun twosum (a, b) =
  let
    val s = (Unsynchronized.! (Unsynchronized.ref (Real.+ (a, b))));
    val an = (Unsynchronized.! (Unsynchronized.ref (Real.- (s, b))));
    val bn = (Unsynchronized.! (Unsynchronized.ref (Real.- (s, an))));
    val da = (Unsynchronized.! (Unsynchronized.ref (Real.- (a, an))));
    val db = (Unsynchronized.! (Unsynchronized.ref (Real.- (b, bn))));
    val aa = (Unsynchronized.! (Unsynchronized.ref (Real.+ (da, db))));
  in
    (s, aa)
  end;

val test_result : real * real = twosum test_input;

fun fst (x1, x2) = x1;

val s : real = fst test_result;

fun snd (x1, x2) = x2;

fun println x = let
                  val _ = TextIO.print x;
                in
                  TextIO.print "\n"
                end;

fun test () =
  let
    val _ = TextIO.print "a = ";
    val _ = println (Real.toString a);
    val _ = TextIO.print "b = ";
    val _ = println (Real.toString b);
    val _ = TextIO.print "r = ";
    val _ = TextIO.print (Real.toString (Real.+ (a, b)));
    val _ = println " (the float closest to a+b)";
    val _ = TextIO.print "s = ";
    val _ = println (Real.toString s);
    val _ = TextIO.print "t = ";
    val _ = println (Real.toString (snd test_result));
  in
    println "done"
  end;

end; (*struct Test*)
