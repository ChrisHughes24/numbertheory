import .preliminary
open finset nat multiplicity

section question

variables {x m n : ℕ} (hx1 : 1 < x) (hm1 : 1 < m)
  (hxmn : (x ^ m + 1) ∣ (x + 1)^n)
include hxmn

lemma dvd_x_add_one_of_dvd_x_pow_m_add_one {p : ℕ} (hp : p.prime) :
  p ∣ x^m + 1 → p ∣ x + 1 :=
λ h, hp.dvd_of_dvd_pow (dvd_trans h hxmn)

section m_odd

variable (hm2 : even m)
include hm2

lemma eq_two_of_prime_of_dvd_x_pow_add_one {p : ℕ} (hp : p.prime)
  (hdvd : p ∣ x^m + 1) : p = 2 :=
have hpx1 : p ∣ x + 1, from dvd_x_add_one_of_dvd_x_pow_m_add_one hxmn hp hdvd,
have hxp : (x : zmodp p hp) = -1,
  by rwa [← sub_eq_zero, sub_neg_eq_add, ← nat.cast_one, ← nat.cast_add,
    zmodp.eq_zero_iff_dvd_nat],
have hxmp : (x^m + 1 : zmodp p hp) = 2,
  by rw [hxp, neg_one_pow_eq_pow_mod_two, even_iff.1 hm2, _root_.pow_zero]; norm_num,
have h20 : (2 : zmodp p hp) = 0,
  by rwa [← hxmp, ← nat.cast_one, ← nat.cast_pow, ← nat.cast_add,
    zmodp.eq_zero_iff_dvd_nat],
by_contradiction (λ hp2 : p ≠ 2, zmodp.prime_ne_zero hp prime_two hp2 (by simpa using h20))

include hx1

lemma x_odd : ¬even x :=
let p := min_fac (x^m + 1) in
have hpp : p.prime, from min_fac_prime (ne_of_gt (succ_lt_succ (nat.pow_pos (by linarith) _))),
have hpdvd : p ∣ x^m + 1, from min_fac_dvd _,
have hp2 : p = 2, from eq_two_of_prime_of_dvd_x_pow_add_one hxmn hm2 hpp hpdvd,
have heven : even (x + 1),
  from dvd_x_add_one_of_dvd_x_pow_m_add_one hxmn prime_two (hp2 ▸ hpdvd),
by simpa with parity_simps using heven

lemma x_pow_add_eq_mod_four_eq_two : (x^m + 1 : zmod 4) = 2 :=
have ∀ y : zmod 4, y.val % 2 = 1 → y^2 + 1 = 2, from dec_trivial,
begin
  have hm2' := hm2,
  cases hm2 with k hk,
  rw hk,
  rw [mul_comm, pow_mul],
  refine this _ _,
  erw [← nat.cast_pow, zmod.val_cast_nat, mod_mul_left_mod (x^k) 2 2,
    ← mod_two_ne_zero, ← even_iff, even_pow, not_and_distrib],
  exact or.inl (x_odd hx1 hxmn hm2'),
end

lemma x_pow_m_add_one_eq_2 : x^m + 1 = 2 :=
let p := min_fac (x^m + 1) in
have hpdvd : p ∣ x^m + 1, from min_fac_dvd _,
have hpp : p.prime, from min_fac_prime (ne_of_gt (succ_lt_succ (nat.pow_pos (by linarith) _))),
have hp2 : p = 2, from eq_two_of_prime_of_dvd_x_pow_add_one hxmn hm2 hpp hpdvd,
let q := min_fac ((x^m + 1) / 2) in
have hqdvd : q ∣ (x^m + 1) / 2, from min_fac_dvd _,
have hqq : ¬q.prime,
  from assume hq,
  have hq2 : q = 2, from eq_two_of_prime_of_dvd_x_pow_add_one hxmn hm2 hq
    (dvd_trans hqdvd (div_dvd_of_dvd (hp2 ▸ hpdvd))),
  let ⟨r, hr⟩ := hqdvd in
  have h4 : 4 ∣ x^m + 1,
    from ⟨r, by rw [← nat.mul_div_cancel' hpdvd, hp2, hr, hq2, ← mul_assoc]; refl⟩,
  begin
    erw [← @zmod.eq_zero_iff_dvd_nat ⟨4, succ_pos _⟩, nat.cast_add, nat.cast_pow, nat.cast_one,
      x_pow_add_eq_mod_four_eq_two hx1 hxmn hm2] at h4,
    exact absurd h4 dec_trivial
  end,
by rw [← nat.mul_div_cancel' hpdvd, hp2, not_imp_comm.1 min_fac_prime hqq, mul_one]

include hm1

lemma m_odd : false :=
lt_irrefl 2 $
  calc 2 < x^m + 1 : succ_lt_succ (show x ^ 0 < x ^ m,
    by rw [← nat.pow_eq_pow, ← nat.pow_eq_pow]; exact pow_lt_pow hx1 (by linarith))
  ... = 2 : x_pow_m_add_one_eq_2 hx1 hxmn hm2

end m_odd

open polynomial

include hx1 hm1

lemma x_add_one_dvd_x_pow_add_one : x + 1 ∣ x^m + 1 :=
have (X : polynomial ℤ) + 1 ∣ X ^ m + 1,
  by rw [← C_1, ← sub_neg_eq_add, ← C_neg, dvd_iff_is_root, is_root, eval_add, eval_C, eval_pow,
    eval_X, neg_one_pow_eq_pow_mod_two, not_even_iff.1 (m_odd hx1 hm1 hxmn), _root_.pow_one,
    neg_add_self],
let ⟨p, hp⟩ := this in
int.coe_nat_dvd.1 ⟨(p.eval (x : ℤ)), by simpa [-add_comm] using congr_arg (eval (x : ℤ)) hp⟩

omit hx1 hm1 hxmn

lemma prime_dvd_choose {p : ℕ} (hp : p.prime) {r t i : ℕ} (hm1 : m % 2 = 1) (hi2 : 2 ≤ i)
  (hpr : p ^ r ∣ m) : p ^ (r + t + 2) ∣ choose m i * p^((t + 1) * i) :=
have hit : t + 2 ≤ (t + 1) * i,
  by rw [add_mul, one_mul]; exact add_le_add
    (le_mul_of_one_le_right' (nat.zero_le _) (by linarith)) hi2,
if hp2 : p = 2
then have hr : r = 0,
  begin
    subst hp2,
    cases r, { refl },
    { rw [nat.pow_succ] at hpr,
      rw [← mod_two_ne_zero, ← dvd_iff_mod_eq_zero] at hm1,
      exact false.elim (hm1 (dvd_trans (by simp) hpr)) }
  end,
  begin
    subst hr, simp only [zero_add, add_mul, one_mul],
    exact dvd_mul_of_dvd_right (pow_dvd_pow _
      (add_le_add (by conv_lhs {rw ← mul_one t}; exact mul_le_mul (le_refl _)
        (by linarith) zero_le_one (nat.zero_le _)) hi2)) _
  end
else
have ¬p ^ ((t + 1) * i - (t + 2) + 1) ∣ i,
  from
  if ht0 : t = 0
  then begin
    subst ht0,
    simp only [add_zero, zero_add, nat.pow_one, one_mul, nat.pow_add],
    show ¬p ^ (i - 2 + 1) ∣ i,
    { assume h : p ^ (i - 2 + 1) ∣ i,
      have hpi : p ^ (i - 2 + 1) ≤ i, from le_of_dvd (by linarith) h,
      exact not_lt_of_ge hpi
        (calc i = i - 2 + 2 : by rw [nat.sub_add_cancel hi2]
          ... < p ^ (i - 2) + 2 * 1 : add_lt_add_of_lt_of_le
            (nat.lt_pow_self hp.one_lt _) (le_refl _)
          ... ≤ p ^ (i - 2) + 2 * p ^ (i - 2) : add_le_add (le_refl _)
            (nat.mul_le_mul_left _ (nat.pow_pos hp.pos _))
          ... = 3 * p ^ (i - 2) : by simp [bit0, bit1, add_mul]
          ... ≤ p * p ^ (i - 2) : nat.mul_le_mul_right
            _ (succ_le_of_lt $ lt_of_le_of_ne hp.two_le (ne.symm hp2))
          ... = p ^ (i - 2 + 1) : by rw [nat.pow_succ, mul_comm]) }
  end
  else
    have i ≤ (t + 1) * i - (t + 2) + 1,
      begin
        rw [← nat.sub_add_comm hit, add_mul, one_mul, show 2 = 1 + 1, from rfl],
        refine nat.le_sub_left_of_add_le _,
        rw [add_assoc, add_right_comm, ← add_assoc, add_le_add_iff_right,
          ← add_assoc, add_le_add_iff_right],
        cases i with i, { exact absurd hi2 dec_trivial },
        { rw [mul_succ],
          exact add_le_add (le_mul_of_one_le_right' (nat.zero_le _) (le_of_succ_le_succ hi2))
            (nat.pos_of_ne_zero ht0) }
      end,
    mt (dvd_trans (nat.pow_dvd_pow _ this))
      (mt (le_of_dvd (by linarith)) (not_le_of_gt (nat.lt_pow_self hp.one_lt _))),
begin
  rw [add_assoc, nat.pow_add, ← nat.sub_add_cancel hit, nat.pow_add _ (_ - _), ← mul_assoc,
    nat.mul_dvd_mul_iff_right (nat.pow_pos hp.pos _)],
  exact hp.pow_dvd_choose_mul_pow (by linarith) hpr this
end

include hx1 hm1 hxmn

lemma prime_dvd_m {p : ℕ} (hp : p.prime) : ∀ {r s t : ℕ} (ht : p ^ t ∣ x + 1) (ht' : ¬p ^ (t + 1) ∣ x + 1)
  (hst : p ^ (s + t) ∣ x^m + 1) (hrs : r ≤ s), p ^ r ∣ m
| 0     s     t     ht ht' hst hrs := by simp
| r     0     0     ht ht' hst hrs := by simp * at *
| r     (s+1) 0     ht ht' hst hrs := false.elim $ ht' $
  dvd_x_add_one_of_dvd_x_pow_m_add_one hxmn (by simpa using hp)
    (dvd_trans (nat.pow_dvd_pow _ (nat.succ_pos _)) hst)
| (r+1) s     (t+1) ht ht' hst hrs :=
let ⟨k, hk⟩ := ht in
have hpk : ¬p ∣ k, from λ hpk, ht'
  (by rw [nat.pow_succ, hk]; exact mul_dvd_mul (dvd_refl _) hpk),
have hxm_eq_kpt : (x^m + 1 : ℤ) = (k * p ^ (t+1) - 1)^m + 1,
  by rw [← int.coe_nat_inj', int.coe_nat_add, ← eq_sub_iff_add_eq] at hk;
    rw [hk]; simp [mul_comm],
have hmeven : even (m - 1),
  from suffices even (m - 1 + 1 + 1), by simpa with parity_simps,
    by simp [nat.sub_add_cancel (le_of_lt hm1), m_odd hx1 hm1 hxmn] with parity_simps,
have hxm_eq_sum : (x^m + 1 : ℤ) = m * k * p ^ (t+1) + (Ico 2 m.succ).sum
    (λ i, choose m i * p^((t+1) * i) * (k^i * (-1) ^ (m - i))),
  begin
    rw [hxm_eq_kpt, sub_eq_add_neg, add_pow, ← Ico.zero_bot, sum_eq_sum_Ico_succ_bot (succ_pos _),
      sum_eq_sum_Ico_succ_bot (succ_lt_succ (lt_trans zero_lt_one hm1)),
      nat.sub_zero, neg_one_pow_eq_pow_mod_two, not_even_iff.1 (m_odd hx1 hm1 hxmn),
      @neg_one_pow_eq_pow_mod_two _ _ (m - 1), even_iff.1 hmeven],
    simp [mul_comm, (pow_mul _ _ _).symm, mul_assoc, mul_left_comm, _root_.mul_pow],
    simp only [mul_comm, mul_left_comm, mul_assoc],
  end,
have hpr : p ^ r ∣ m, from prime_dvd_m ht ht' hst (le_of_succ_le hrs),
have hdvd_sum : (p : ℤ) ^ (r + (t+1) + 1) ∣ (Ico 2 m.succ).sum
    (λ i, choose m i * p^((t+1) * i) * (k^i * (-1 : ℤ) ^ (m - i))),
  from dvd_sum (λ i hi, begin
    refine dvd_mul_of_dvd_left _ _,
    simp only [(int.coe_nat_pow _ _).symm, (int.coe_nat_mul _ _).symm, int.coe_nat_dvd],
    convert prime_dvd_choose hp (not_even_iff.1 (m_odd hx1 hm1 hxmn)) (Ico.mem.1 hi).1 hpr
  end),
have hdvd_m : (p : ℤ) ^ (r + (t+1) + 1) ∣ m * k * p ^ (t+1),
  from (dvd_add_iff_left hdvd_sum).2 begin
    rw [← hxm_eq_sum],
    simp only [(int.coe_nat_pow _ _).symm, int.coe_nat_dvd,
      int.coe_nat_one.symm, (int.coe_nat_add _ _).symm],
    exact dvd_trans (nat.pow_dvd_pow _ (by linarith)) hst,
  end,
have hdvd_mk : p^(r + 1) ∣ m * k,
  from nat.dvd_of_mul_dvd_mul_right (nat.pow_pos hp.pos (t + 1))
    (int.coe_nat_dvd.1 $ by simpa [(_root_.pow_add _ _ _).symm] using hdvd_m),
hp.pow_dvd_of_dvd_mul_of_not_dvd hdvd_mk hpk

lemma x_pow_add_one_div_x_add_one_dvd_m : (x^m + 1) / (x + 1) ∣ m :=
dvd_of_forall_prime_pow_dvd $
  (λ (p r : ℕ) (hp : p.prime) h,
    have htdom : (multiplicity p (x + 1)).dom, from finite_nat_iff.2 ⟨ne_of_gt hp.one_lt, succ_pos _⟩,
    let t := (multiplicity p (x + 1)).get htdom in
    have ht : p ^ t ∣ x + 1, by rw [← nat.pow_eq_pow]; exact pow_multiplicity_dvd _,
    have hrt : p ^ (r + t) ∣ (x^m + 1),
      by rw [nat.pow_add, ← nat.div_mul_cancel (x_add_one_dvd_x_pow_add_one hx1 hm1 hxmn)];
        exact mul_dvd_mul h ht,
    have ht' : ¬p ^ (t + 1) ∣ x + 1,
      by rw [← nat.pow_eq_pow, ← multiplicity_lt_iff_neg_dvd, ← enat.coe_get htdom, enat.coe_lt_coe];
        exact nat.lt_succ_self _,
    prime_dvd_m hx1 hm1 hxmn hp ht ht' hrt (le_refl _))

lemma x_pow_add_one_le_m_mul_x_add_m : x ^ m + 1 ≤ x * m + m  :=
le_of_dvd (by linarith) $
let ⟨q, hq⟩ := x_pow_add_one_div_x_add_one_dvd_m hx1 hm1 hxmn in
begin
  rw [show x * m + m = (x + 1) * m, by simp [add_mul]],
  conv_rhs {rw hq},
  rw [← mul_assoc, nat.mul_div_cancel' (x_add_one_dvd_x_pow_add_one hx1 hm1 hxmn)],
  simp
end

lemma m_eq_three : m = 3 :=
have x ^ m + 1 ≤ x * m + m, from x_pow_add_one_le_m_mul_x_add_m hx1 hm1 hxmn,
have h4m : ¬ 4 ≤ m,
  from λ h, let ⟨m', hm'⟩ := le_iff_exists_add.1 h in
  let ⟨x', (hx' : x = 2 + x')⟩ := le_iff_exists_add.1 (nat.succ_le_of_lt hx1) in
  have h32 : m' + 4 ≤ 32 * (x' + 2) ^ m',
    from calc m' + 4 ≤ (x' + 2) ^ m' + 4 * 1:
        add_le_add (le_of_lt $ nat.lt_pow_self dec_trivial _) (le_refl _)
      ... ≤ (x' + 2) ^ m' + 4 * (x' + 2) ^ m' :
        add_le_add (le_refl _) (mul_le_mul_left _ (nat.pow_pos (succ_pos _) _))
      ... = 5 * (x' + 2) ^ m' : by ring
      ... ≤ 32 * (x' + 2) ^ m' : mul_le_mul_right _ dec_trivial,
  have h16 : 3 * m' + 12 < 16 * (x' + 2) ^ m',
    from calc 3 * m' + 12 ≤ 3 * (x' + 2) ^ m' + 12 * 1 :
        add_le_add (nat.mul_le_mul_left _ (le_of_lt $ lt_pow_self dec_trivial _)) (le_refl _)
      ... ≤ 3 * (x' + 2) ^ m' + 12 * (x' + 2) ^ m' :
        add_le_add (le_refl _) (mul_le_mul_left _ (nat.pow_pos (succ_pos _) _))
      ... = 15 * (x' + 2) ^ m' : by ring
      ... < 16 * (x' + 2) ^ m' :
        (mul_lt_mul_right (nat.pow_pos (succ_pos _) _)).2 dec_trivial,
  begin
    clear_aux_decl, substs hm' hx',
    exact not_lt_of_ge this
      (calc   (2 + x') * (4 + m') + (4 + m')
            = x' * (m' + 4) + (3 * m' + 12) : by ring
        ... < x' * (32  * (x' + 2) ^ m') + 16 * (x' + 2) ^ m' :
          add_lt_add_of_le_of_lt (mul_le_mul_left _ h32) h16
        ... ≤ (x' * (32  * (x' + 2) ^ m') + 16 * (x' + 2) ^ m') +
            (1 + (x' + 2) ^ m' * (x' ^ 4 + 8 * x' ^ 3 + 24 * x' ^ 2)) :
          le_add_right (le_refl _)
        ... = (2 + x') ^ (4 + m') + 1 : by simp [nat.pow_add]; ring)
  end,
have m_odd : ¬ even m, from m_odd hx1 hm1 hxmn,
begin
  clear hxmn this,
  rw [not_le] at h4m,
  revert m_odd hm1, revert m,
  exact dec_trivial
end

lemma x_eq_two : x = 2 :=
have hm3 : m = 3, from m_eq_three hx1 hm1 hxmn,
have x ^ m + 1 ≤ x * m + m, from x_pow_add_one_le_m_mul_x_add_m hx1 hm1 hxmn,
have h3x : ¬ 3 ≤ x, from λ h3x,
  begin
    rcases le_iff_exists_add.1 h3x with ⟨x', rfl⟩,
    subst hm3,
    exact not_lt_of_ge this
      (calc (3 + x') * 3 + 3 < x' ^ 3 + 9 * x' ^ 2 + 27 * x' + 28 : by linarith
        ... = (3 + x') ^ 3 + 1 : by ring)
  end,
by linarith

omit hxmn

lemma question_4 : x ^ m + 1 ∣ (x + 1) ^ n ↔ (x = 2 ∧ m = 3 ∧ 2 ≤ n) :=
iff.intro
  (λ hxmn,
    have hm3 : m = 3, from m_eq_three hx1 hm1 hxmn,
    have hx2 : x = 2, from x_eq_two hx1 hm1 hxmn,
    ⟨hx2, hm3, begin
      substs hm3 hx2,
      refine le_of_not_lt (λ h2n, _),
      revert hxmn, revert n,
      exact dec_trivial
    end⟩)
  (begin
    rintros ⟨rfl, rfl, hn2⟩,
    rw [← nat.add_sub_cancel' hn2, nat.pow_add],
    exact dvd_mul_right _ _
  end)

end question