theory Mult
  imports Main Add
begin

(*  mult: \<nat> \<times> \<nat> \<rightarrow> \<nat>  *)
(*  requer \<top>  *)
(*  garante mult(x, y) = x \<^emph> y  *)
(*  mult (x, y) = 0, se y = 0  *)
(*  mult (x, y) = x + mult (x, y − 1), se y > 0  *)

primrec mult::"nat \<Rightarrow> nat \<Rightarrow> nat"
where
  mult01: "mult x 0 = 0"|
  mult02: "mult x (Suc y) = add x (mult x y)"

value "mult 2 2"
value "mult 1 2"
value "mult 2 0"
value "mult 0 1"

end

