theory Mult
  imports Main Add
begin

thm nat.induct
print_statement nat.induct

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

(*  \<forall>x \<in> \<nat>. \<forall>y \<in> \<nat>: mult(x, y) = x \<^emph> y  *)
theorem multT1:"\<forall>x. mult x y = x * y"
proof(induct y)
  show "\<forall>x. mult x 0 = x * 0"
  proof (rule allI)
    fix x0::nat
    have "mult x0 0 = 0" by (simp only:mult01)
    also have "... = x0 * 0" by (simp only:algebra)
    finally show "mult x0 0 = x0 * 0" by simp
  qed
next
  fix y0::nat
  assume HIP:"\<forall>x. mult x y0 = x * y0"
  show "\<forall>x. mult x (Suc y0) = x * (Suc y0)"
  proof (rule allI)
    fix x0::nat
    have "mult x0 (Suc y0) = add x0 (mult x0 y0)" by (simp only:mult02)
    also have "... = x0 + (mult x0 y0)" by (simp only:addT1)
    also have "... = x0 + x0 * y0" by (simp only:HIP)
    also have "... = x0 * (y0 + 1)" by algebra
    also have "... = x0 * (Suc y0)" by simp
    finally show "mult x0 (Suc y0) = x0 * (Suc y0)" by simp
  qed
qed

(*  \<forall>x \<in> \<nat>. \<forall>y \<in> \<nat>: mult(x, y) = mult(y, x)  *)
theorem multT2:"\<forall>x. mult x y = mult y x"
proof(induct y)
  show "\<forall>x. mult x 0 = mult 0 x"
  proof (rule allI)
    fix x0::nat
    have "mult x0 0 = 0" by (simp only:mult01)
    also have "... = 0 * x0" by (simp only:algebra)
    also have "... = mult 0 x0" by (simp only:multT1)
    finally show "mult x0 0 = mult 0 x0" by simp
  qed
next
  fix y0::nat
  assume HIP:"\<forall>x. mult x y0 = mult y0 x"
  show "\<forall>x. mult x (Suc y0) = mult (Suc y0) x"
  proof (rule allI)
    fix x0::nat
    have "mult x0 (Suc y0) = add x0 (mult x0 y0)" by (simp only:mult02)
    also have "... = x0 + (mult x0 y0)" by (simp only:addT1)
    also have "... = x0 + x0 * y0" by (simp only:multT1)
    also have "... = x0 * (y0 + 1)" by algebra
    also have "... = x0 * (Suc y0)" by simp
    also have "... = (Suc y0) * x0" by simp
    also have "... = mult (Suc y0) x0" by (simp only:multT1)
    finally show "mult x0 (Suc y0) = mult (Suc y0) x0" by simp
  qed
qed

(*  \<forall>x \<in> \<nat>: mult(1, x) = x  *)
theorem multT4:"mult 1 x = x"
proof(induct x)
  show "mult 1 0 = 0"
  proof -
    show "mult 1 0 = 0" by (simp only:mult01) 
  qed
next
  fix x0::nat
  assume HIP:"mult 1 x0 = x0"
  show "mult 1 (Suc x0) = Suc x0"
  proof -
    have "mult 1 (Suc x0) = add 1 (mult 1  x0)" by (simp only:mult02)
    also have "... = add 1 x0" by (simp only:HIP)
    also have "... = Suc x0" by (simp only:addT0)
    finally show "mult 1 (Suc x0) = Suc x0" by simp
  qed
qed

(*  \<forall>x \<in> \<nat>: mult(x, 1) = x  *)
theorem multT3:"mult x 1 = x"
proof(induct x)
  show "mult 0 1 = 0"
  proof -
    have "mult 0 1 = 0 * 1" by (simp only:multT1)
    also have "... = 0" by arith
    finally show "mult 0 1 = 0" by simp
  qed
next
  fix x0::nat
  assume HIP:"mult x0 1 = x0"
  show "mult (Suc x0) 1 = Suc x0"
  proof -
    have "mult (Suc x0) 1 = mult 1 (Suc x0)" by (simp only:multT2)
    also have "... = Suc x0" by (simp only:multT4)
    finally show "mult (Suc x0) 1 = Suc x0" by simp
  qed
qed

(*  \<forall>x \<in> \<nat>. \<forall>y \<in> \<nat>. \<forall>z \<in> \<nat>: mult(x, mult(y, z)) = mult(mult(x, y), z)  *)
theorem multT5:"\<forall>x. \<forall>y. mult x (mult y z) = mult (mult x y) z"
proof(induction z)
  show "\<forall>x. \<forall>y. mult x (mult y 0) = mult (mult x y) 0"
  proof(rule allI, rule allI)
    fix x0::nat and y0::nat
    have "mult x0 (mult y0 0) = mult x0 0" by (simp only:mult01)
    also have "... = mult (mult x0 y0) 0" by (simp only:mult01)
    finally show "mult x0 (mult y0 0) = mult (mult x0 y0) 0" by simp
  qed
next
  fix z0::nat
  assume HI:"\<forall>x y. mult x (mult y z0) = mult (mult x y) z0"
  show "\<forall>x y. mult x (mult y (Suc z0)) = mult (mult x y) (Suc z0)"
  proof(rule allI, rule allI)
    fix x0::nat and y0::nat
    have "mult x0 (mult y0 (Suc z0)) = x0 * (mult y0 (Suc z0))" by (simp only:multT1)
    also have "... = x0 * y0 * (Suc z0)" by (simp only:multT1)
    also have "... = mult x0 y0 * (Suc z0)" by (simp only:multT1)
    also have "... = mult (mult x0 y0) (Suc z0)" by (simp only:multT1)
    finally show "mult x0 (mult y0 (Suc z0)) = mult (mult x0 y0) (Suc z0)" by simp
  qed
qed