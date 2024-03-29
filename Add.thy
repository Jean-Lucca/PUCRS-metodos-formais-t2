theory Add
imports Main
begin

(*funcao recursiva de somar nat*)
primrec add::"nat \<Rightarrow> nat \<Rightarrow> nat"
where
  add01: "add x 0 = x" |
  add02: "add x (Suc y) = Suc (add x y)"

theorem th_add01as:"\<forall>x y. add (add x y) z = add x (add y z)"
apply(induction z)
apply(simp)
apply(simp)
  done

theorem addT0:"add 1 x = Suc x"
proof(induct x)
  show "add 1 0 = Suc 0"
  proof -
    have "add 1 0 = 1" by (simp only:add01)
    also have "... = Suc 0" by (simp only:algebra)
    finally show "add 1 0 = Suc 0" by simp
  qed
next
  fix x0::nat
  assume HIP:"add 1 x0 = Suc x0"
  show "add 1 (Suc x0) = Suc (Suc x0)"
  proof -
    have "add 1 (Suc x0) = Suc (add 1 x0)" by (simp only:add02)
    also have "... = Suc (Suc x0)" by (simp only:HIP)
    finally show "add 1 (Suc x0) = Suc (Suc x0)" by simp
  qed
qed

theorem addT1:"\<forall>x. add x y = x + y"
proof (induct y)
  show "\<forall>x. add x 0 = x + 0"
  proof (rule allI)
    fix x0::nat
    have "add x0 0 = x0" by (simp only:add01)
    also have "... = x0 + 0" by simp
    finally show "add x0 0 = x0 + 0" by simp
  qed
next
  fix y0::nat
  assume HIP:"\<forall>x. add x y0 = x + y0"
  show "\<forall>x. add x (Suc y0) = x + (Suc y0)"
  proof (rule allI)
    fix x0::nat
    have "add x0 (Suc y0) = Suc (add x0 y0)" by (simp only:add02)
    also have "... = Suc (x0 + y0)" by (simp only:HIP)
    also have "... = x0 + (Suc y0)" by simp
    finally show "add x0 (Suc y0) = x0 + (Suc y0)" by simp
  qed
qed

inductive ev::"nat \<Rightarrow> bool"
where
  ev0: "ev 0" |
  ev1: "ev n \<Longrightarrow> ev (Suc (Suc n))"

thm "ev.induct"

lemma "ev (Suc(Suc(Suc(Suc 0))))"
apply(rule ev1)
apply(rule ev1)
apply(rule ev0)
done

fun even::"nat \<Rightarrow> bool"
where
  "even 0 = True" |
  "even (Suc 0) = False" |
  "even (Suc(Suc n)) = even n"

theorem "ev n \<Longrightarrow> even n"
apply(induct rule: ev.induct)
apply(auto)
done

theorem "even n \<Longrightarrow> ev n"
apply(induct rule: even.induct)
apply(simp add: ev0)
apply(simp)
apply(simp add: ev1)
done

theorem "ev n \<Longrightarrow> \<exists>k. n = 2*k"
apply(induct rule: ev.induct)
apply(simp)
apply(arith)
done

(*provas isar*)

thm nat.induct
print_statement nat.induct

theorem th_add01isar:"\<forall>x y. add (add x y) z = add x (add y z)"
proof (induction z)
show "\<forall>x y. add (add x y) 0 = add x (add y 0)"
by simp
next
fix x0::nat
assume HI:"\<forall>x y. add (add x y) x0 = add x (add y x0)"
show "\<forall>x y. add (add x y) (Suc x0) = add x (add y (Suc x0))"
by (simp add:HI)
qed

theorem th_add01isar2:"\<forall>x y. add (add x y) z = add x (add y z)"
proof (induction z)
show "\<forall>x y. add (add x y) 0 = add x (add y 0)"
proof(rule allI, rule allI)
fix x0::nat and y0::nat
have "add (add x0 y0) 0 = add x0 y0"
by (simp only:add01)
also have "... = add x0 (add y0 0)"
by (simp only:add01)
finally show "add (add x0 y0) 0 = add x0 (add y0 0)"
by simp
qed
next
fix z0::nat
assume HI:"\<forall>x y. add (add x y) z0 = add x (add y z0)"
show "\<forall>x y. add (add x y)(Suc z0) = add x (add y (Suc z0))"
proof(rule allI, rule allI)
fix x0::nat and y0::nat
have "add (add x0 y0)(Suc z0) = Suc(add (add x0 y0) z0)" by (simp only:add02)
also have "... = Suc(add x0 (add y0 z0))" by (simp only:HI)
also have "... = add x0 (Suc (add y0 z0))" by (simp only:add02)
also have "... = add x0 (add y0 (Suc z0))" by (simp only:add02)
finally show "add (add x0 y0)(Suc z0) = add x0 (add y0 (Suc z0))" by simp
qed
qed












end

