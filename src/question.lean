import data.nat.choose ring_theory.multiplicity algebra.gcd_domain data.nat.modeq tactic.linarith
import data.zmod.basic data.nat.parity data.polynomial
open finset nat multiplicity

lemma not_even_iff {n : ℕ} : ¬ even n ↔ n % 2 = 1 :=
by rw [even_iff, mod_two_ne_zero]

lemma dvd_sum {α β : Type*} [comm_semiring α] {s : finset β}
  {f : β → α} {a : α} : (∀ x ∈ s, a ∣ f x) → a ∣ s.sum f :=
by classical; exact finset.induction_on s (by simp)
  (λ b s hbs ih h, by rw [sum_insert hbs];
     exact dvd_add (h b (by simp))
       (ih (λ x hx, h x (by finish))))

lemma pow_dvd_iff_le_card_pow_dvd {m n r : ℕ} (hm1 : 1 < m) (hn0 : 0 < n) : m ^ r ∣ n ↔
  r ≤ ((finset.Ico 1 n).filter (λ i, m ^ i ∣ n)).card :=
⟨λ h, calc r = (Ico 1 (r+1)).card : by simp
  ... ≤ _ : card_le_of_subset
    (begin
      assume x hx,
      simp only [Ico.mem, mem_filter] at *,
      exact ⟨⟨hx.1, lt_of_le_of_lt (le_of_lt_succ hx.2)
          (lt_of_lt_of_le (lt_pow_self hm1 _) (le_of_dvd hn0 h))⟩,
        dvd_trans (nat.pow_dvd_pow _ (le_of_lt_succ hx.2)) h⟩,
    end),
λ hr, by_contradiction $ λ h, not_lt_of_ge hr $
  calc ((finset.Ico 1 n).filter (λ i, m ^ i ∣ n)).card <
        (range r).card : card_lt_card
      ⟨begin
        assume x hx,
        simp only [mem_range, mem_filter] at *,
        exact lt_of_not_ge (λ hxr, h (dvd_trans (nat.pow_dvd_pow _ hxr) hx.2))
      end, λ hsub,
        have h0r : 0 < r, from nat.pos_of_ne_zero (λ hr0, by simp * at *),
        by simpa using hsub (mem_range.2 h0r)⟩
  ... = r : card_range _ ⟩

lemma card_pow_dvd_eq_multiplicity {m n : ℕ} (hm1 : 1 < m) (hn0 : 0 < n) :
  ↑((finset.Ico 1 n).filter (λ i, m ^ i ∣ n)).card = multiplicity m n :=
multiplicity.unique
  (by rw [nat.pow_eq_pow, pow_dvd_iff_le_card_pow_dvd hm1 hn0])
  (by rw [nat.pow_eq_pow, pow_dvd_iff_le_card_pow_dvd hm1 hn0]; simp)

lemma sum_Ico_succ_top {α : Type*} [add_comm_monoid α] {a b : ℕ} (hab : a ≤ b) (f : ℕ → α) :
  (Ico a (b + 1)).sum f = (Ico a b).sum f + f b :=
by rw [Ico.succ_top hab, sum_insert Ico.not_mem_top, add_comm]

lemma Ico_succ_bot {a b : ℕ} (hab : a < b) : insert a (Ico (succ a) b) = Ico a b :=
begin
  simp only [finset.ext, succ_le_iff, mem_insert, Ico.mem, hab],
  assume i,
  split,
  { rintro ⟨rfl | h, hab⟩,
    { simp * },
    { exact ⟨le_of_lt a_1.1, a_1.2⟩ } },
  { rintros ⟨hai, hab⟩,
    rcases lt_or_eq_of_le hai with hai | rfl,
    { simp * },
    { simp * } }
end

lemma sum_eq_sum_Ico_succ_bot {α : Type*} [add_comm_monoid α] {a b : ℕ} (hab : a < b)
  (f : ℕ → α) : (Ico a b).sum f = f a + (Ico (a + 1) b).sum f :=
have ha : a ∉ Ico (a + 1) b, by simp,
by rw [← sum_insert ha, Ico_succ_bot hab]

lemma nat.prime.multiplicity_one {p : ℕ} (hp : p.prime) :
  multiplicity p 1 = 0 :=
by rw [multiplicity.one_right (mt is_unit_nat.mp (ne_of_gt hp.one_lt))]

lemma nat.prime.multiplicity_mul {p m n : ℕ} (hp : p.prime) :
  multiplicity p (m * n) = multiplicity p m + multiplicity p n :=
by rw [int.coe_nat_multiplicity, int.coe_nat_multiplicity,
  int.coe_nat_multiplicity, int.coe_nat_mul, multiplicity.mul (nat.prime_iff_prime_int.1 hp)]

lemma nat.prime.multiplicity_pow {p m n : ℕ} (hp : p.prime) :
  multiplicity p (m ^ n) = add_monoid.smul n (multiplicity p m) :=
by induction n; simp [nat.pow_succ, hp.multiplicity_mul, *, hp.multiplicity_one, succ_smul]

lemma nat.prime.multiplicity_self {p : ℕ} (hp : p.prime) : multiplicity p p = 1 :=
have h₁ : ¬ is_unit (p : ℤ), from mt is_unit_int.1 (ne_of_gt hp.one_lt),
have h₂ : (p : ℤ) ≠ 0, from int.coe_nat_ne_zero.2 hp.ne_zero,
by rw [int.coe_nat_multiplicity, multiplicity_self h₁ h₂]

lemma nat.prime.multiplicity_pow_self {p n : ℕ} (hp : p.prime) : multiplicity p (p ^ n) = n :=
by induction n; simp [hp.multiplicity_one, nat.pow_succ, hp.multiplicity_mul, *,
  hp.multiplicity_self, succ_eq_add_one]

lemma nat.prime.pow_dvd_fact {p : ℕ} : ∀ {n r : ℕ} (hp : p.prime),
   p ^ r ∣ fact n ↔ r ≤ (Ico 1 (n+1)).sum (λ i, n / p ^ i)
| 0     0     hp := by simp
| 0     (r+1) hp := by simp [nat.pow_succ, nat.mul_eq_one_iff, ne_of_gt hp.one_lt]
| (n+1) r     hp :=
have (Ico 1 (n+1)).sum (λ i, (n + 1) / p ^ i) =
  (Ico 1 (n+1)).sum (λ i, n / p ^ i)
    + ((Ico 1 (n+1)).filter (λ i, p^i ∣ (n+1))).card,
  from calc (Ico 1 (n+1)).sum (λ i, (n + 1) / p ^ i)
      = (Ico 1 (n+1)).sum (λ i, n / p ^ i + ite (p^i ∣ (n+1)) 1 0) :
    sum_congr rfl $ λ _ _, by rw nat.succ_div; exact nat.pow_pos hp.pos _
  ... = _ : by rw [sum_add_distrib, sum_ite (λ _, 1) (λ _, 0) (λ x, x)]; simp,
have hnp : (n + 1) / p ^ (n + 1) = 0,
  from (nat.div_eq_zero_iff (nat.pow_pos hp.pos _)).2 (lt_pow_self hp.one_lt _),
begin
  rw [sum_Ico_succ_top (nat.succ_pos _), hnp, this],
  by_cases hr : r ≤  ((Ico 1 (n+1)).filter (λ i, p ^ i ∣ (n + 1))).card,
  { exact iff_of_true
      (dvd_mul_of_dvd_left ((pow_dvd_iff_le_card_pow_dvd hp.one_lt (succ_pos _)).2 hr) _)
      (le_trans hr (le_add_left _ _)) },
  { erw [← @nat.sub_le_right_iff_le_add _ _ (card _), ← hp.pow_dvd_fact],
    conv_rhs { rw [← nat.mul_dvd_mul_iff_left
      (nat.pow_pos hp.pos (((Ico 1 (n+1)).filter (λ i, p^i ∣ (n+1))).card))] },
    split,
    { assume h,
      refine mul_dvd_mul (dvd_refl _) _,
      rw [pow_dvd_iff_le_card_pow_dvd hp.one_lt (fact_pos _), nat.sub_le_right_iff_le_add],
      rw [pow_dvd_iff_le_card_pow_dvd hp.one_lt (fact_pos _)] at h,
      refine le_trans h _,
      rw [← enat.coe_le_coe, enat.coe_add, card_pow_dvd_eq_multiplicity hp.one_lt (fact_pos _),
        card_pow_dvd_eq_multiplicity hp.one_lt (fact_pos _),
        card_pow_dvd_eq_multiplicity hp.one_lt (succ_pos _),
        ← hp.multiplicity_mul, fact_succ, mul_comm] },
    { rw [← nat.pow_add, nat.add_sub_cancel' (le_of_not_le hr)],
      exact function.swap dvd_trans
        (by rw [fact_succ]; exact (nat.mul_dvd_mul_iff_right (fact_pos _)).2
          ((pow_dvd_iff_le_card_pow_dvd hp.one_lt (succ_pos _)).2 (le_refl _))) } },
end

lemma multiplicity_fact {p n : ℕ} (hp : p.prime) :
  multiplicity p (fact n) = ((Ico 1 (n+1)).sum (λ i, n / p ^ i) : ℕ) :=
eq.symm $ multiplicity.unique
  (by rw [nat.pow_eq_pow, hp.pow_dvd_fact])
  (by rw [nat.pow_eq_pow, hp.pow_dvd_fact]; simp)

lemma whatever {p n k : ℕ} (hkn : k ≤ n) (hp : p.prime) :
  multiplicity p (choose n k) + multiplicity p (fact k) + multiplicity p (fact (n - k)) =
  multiplicity p (fact n) :=
by rw [← hp.multiplicity_mul, ← hp.multiplicity_mul, choose_mul_fact_mul_fact hkn]

lemma mod_add_le_mod_add (a b c : ℕ) : (a + b) % c ≤ a % c + b % c :=
if hc0 : c = 0 then by simp [hc0]
else by_contradiction $ λ h, begin
  have := mod_eq_of_lt (lt_trans (lt_of_not_ge h)
    (mod_lt _ (nat.pos_of_ne_zero hc0))),
  rw ← this at h,
  exact h (le_of_eq (nat.modeq.modeq_add (nat.modeq.mod_modeq _ _).symm
    (nat.modeq.mod_modeq _ _).symm))
end

lemma add_div_le_add_div (a b c : ℕ) : a / c + b / c ≤ (a + b) / c :=
if hc0 : c = 0 then by simp [hc0]
else begin
  refine le_of_mul_le_mul_left _ (nat.pos_of_ne_zero hc0),
  refine @nat.le_of_add_le_add_left (a % c + b % c) _ _ _,
  rw [mul_add, add_add_add_comm, mod_add_div, mod_add_div],
  conv_lhs { rw ← mod_add_div (a + b) c },
  exact add_le_add_right (mod_add_le_mod_add _ _ _) _
end

lemma add_div_add_ite_le_add_div (a b c : ℕ) (hc0 : 0 < c):
  a / c + b / c + (if c ∣ a + b ∧ ¬ c ∣ a then 1 else 0) ≤ (a + b) / c :=
if h : c ∣ a + b ∧ ¬ c ∣ a
then
have a % c + b % c = c,
  from have c ∣ a % c + b % c,
    from dvd_of_mod_eq_zero $ by rw [← mod_eq_zero_of_dvd h.1];
      exact nat.modeq.modeq_add (nat.modeq.mod_modeq _ _) (nat.modeq.mod_modeq _ _),
  let ⟨x, hx⟩ := this in
  have a % c + b % c < c * 2,
    by rw [mul_two]; exact add_lt_add (mod_lt _ hc0) (mod_lt _ hc0),
  have hx2 : x < 2, from lt_of_mul_lt_mul_left (by rwa [← hx]) (le_of_lt hc0),
  have hx1 : x = 1, from le_antisymm (le_of_lt_succ hx2)
    (nat.pos_of_ne_zero
      (λ hx0, by clear_aux_decl; simp [*, lt_irrefl, nat.dvd_iff_mod_eq_zero] at *)),
  by simp * at *,
begin
  rw [if_pos h],
  refine le_of_mul_le_mul_left _ hc0,
  refine @le_of_add_le_add_left _ _ (a % c + b % c) _ _ _,
  rw [mul_add, mul_add, mul_one, ← add_assoc, add_add_add_comm, mod_add_div,
    mod_add_div, nat.mul_div_cancel' h.1, this, add_comm]
end
else by rw [if_neg h, add_zero]; exact add_div_le_add_div _ _ _

lemma multiplicity_choose_aux {p n k : ℕ} (hp : p.prime) (hk0 : 0 < k) (hkn : k < n) (hn0 : 0 < n) :
  (Ico 1 (k+1)).sum (λ i, k / p ^ i)
  + (Ico 1 ((n-k) + 1)).sum (λ i, (n - k) / p ^ i)
  + ((finset.Ico 1 n).filter (λ i, p ^ i ∣ n)).card
  ≤ (Ico 1 (n+1)).sum (λ i, n / p ^ i)
  + ((finset.Ico 1 k).filter (λ i, p ^ i ∣ k)).card :=
have h₁ : ∀ k ≤ n, 0 < k → (Ico 1 (k+1)).sum (λ i, k / p ^ i) = (Ico 1 (n+1)).sum (λ i, k / p ^ i),
  from λ k hk hk0, sum_subset ((Ico.subset_iff (succ_lt_succ hk0)).2 ⟨le_refl _, succ_le_succ hk⟩)
    (λ i hin hik, (nat.div_eq_zero_iff (nat.pow_pos hp.pos _)).2 $
      lt_of_lt_of_le (lt_pow_self hp.one_lt _) (le_of_dvd (nat.pow_pos hp.pos _)
        (pow_dvd_pow _ (le_of_lt $ by simp [*, succ_le_iff] at *)))),
have h₂ : ∀ k ≤ n, 0 < k → (finset.Ico 1 k).filter (λ i, p ^ i ∣ k) =
    (finset.Ico 1 (n + 1)).filter (λ i, p ^ i ∣ k),
  from λ k hkn hk0, le_antisymm
    (filter_subset_filter (Ico.subset (le_refl _) (le_trans hkn (le_succ _))))
    (λ x, begin
      simp only [mem_filter, Ico.mem, nat.succ_le_iff, and_imp, true_and, and_true] { contextual := tt },
      assume hx0 hxn hpxk,
      exact lt_of_lt_of_le (nat.lt_pow_self hp.one_lt _) (le_of_dvd hk0 hpxk)
    end),
begin
  rw [h₁ _ (le_of_lt hkn) hk0, h₁ _ (nat.sub_le_self n k) (nat.sub_pos_of_lt hkn),
    h₂ k (le_of_lt hkn) hk0, h₂ n (le_refl _) hn0,
    ← mul_one (card _), ← nat.smul_eq_mul, ← sum_const, sum_filter,
    ← mul_one (card _), ← nat.smul_eq_mul, ← sum_const, sum_filter,
    ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib],
  refine finset.sum_le_sum (λ i hi, _),
  have := add_div_add_ite_le_add_div k (n - k) (p ^ i) (nat.pow_pos hp.pos _),
  rw [nat.add_sub_cancel' (le_of_lt hkn)] at this,
  split_ifs at *; simp * at *; linarith
end

lemma le_multiplicity_choose {p n k : ℕ} (hp : p.prime) (hn0 : 0 < n) (hk0 : 0 < k)
  (hkn : k < n) : multiplicity p n ≤ multiplicity p (choose n k) + multiplicity p k :=
have h₁ : multiplicity p (fact k) + multiplicity p (fact (n - k)) + multiplicity p n
  ≤ multiplicity p (fact n) + multiplicity p k,
  begin
    rw [multiplicity_fact hp, multiplicity_fact hp, multiplicity_fact hp,
      ← card_pow_dvd_eq_multiplicity hp.one_lt hn0,
      ← card_pow_dvd_eq_multiplicity hp.one_lt hk0,
      ← enat.coe_add, ← enat.coe_add, ← enat.coe_add, enat.coe_le_coe],
    exact multiplicity_choose_aux hp hk0 hkn hn0
  end,
have h₂ : ((multiplicity p n).get (finite_nat_iff.2 ⟨ne_of_gt hp.one_lt, hn0⟩) : enat) ≤
    (multiplicity p (choose n k * k)).get (finite_nat_iff.2 ⟨ne_of_gt hp.one_lt,
      mul_pos (choose_pos (le_of_lt hkn)) hk0⟩),
  from enat.coe_le_coe.2 (@le_of_add_le_add_right _ _ _
    ((multiplicity p (fact k * fact (n - k))).get
      (finite_nat_iff.2 ⟨ne_of_gt hp.one_lt, mul_pos (fact_pos _) (fact_pos _)⟩))
    _ begin
      rw [← enat.coe_le_coe],
      simp only [enat.coe_add, enat.coe_get],
      rw [← hp.multiplicity_mul, ← hp.multiplicity_mul, mul_comm _ k,
        mul_assoc k, ← mul_assoc (nat.choose _ _), choose_mul_fact_mul_fact (le_of_lt hkn)],
      simpa [hp.multiplicity_mul] using h₁
    end),
by rwa [enat.coe_get, enat.coe_get, hp.multiplicity_mul] at h₂

lemma nat.prime.pow_dvd_choose_mul_pow {p n k r j : ℕ} (hp : p.prime) (hk0 : 0 < k)
  (hpn : p ^ r ∣ n) (hpjk : ¬ p ^ (j + 1) ∣ k) :
  p ^ r ∣ choose n k * p ^ j :=
if hn0 : n = 0 then by cases k; simp [hn0, choose_zero_succ, lt_irrefl, *] at *
else if hk_eq_n : k = n
then begin
  subst hk_eq_n,
  simp,
  refine nat.pow_dvd_pow _ (le_of_not_gt
    (λ hrj, hpjk (dvd_trans (nat.pow_dvd_pow _ (succ_le_of_lt hrj)) hpn))),
end
else if hn_lt_k : n < k
then by simp [choose_eq_zero_of_lt hn_lt_k]
else have multiplicity p n ≤ multiplicity p (choose n k * p ^ j),
  from calc multiplicity p n ≤ multiplicity p (choose n k) + multiplicity p k :
      le_multiplicity_choose hp (nat.pos_of_ne_zero hn0) hk0 (lt_of_le_of_ne (le_of_not_gt hn_lt_k) hk_eq_n)
    ... ≤ multiplicity p (choose n k) + j :
      add_le_add' (le_refl _) (enat.le_of_lt_add_one
        (by rw [← enat.coe_one, ← enat.coe_add]; rw [← nat.pow_eq_pow] at hpjk;
          exact multiplicity_lt_iff_neg_dvd.2 hpjk))
    ... = _ : by rw [← hp.multiplicity_pow_self, hp.multiplicity_mul],
  begin
    rw [multiplicity_le_multiplicity_iff] at this,
    simp only [nat.pow_eq_pow] at *,
    exact this r hpn
  end

lemma nat.prime.pow_dvd_choose_mul {p n k r : ℕ} (hp : p.prime) (hk0 : 0 < k) (hkn : k < n)
  (hpn : p ^ r ∣ n) :  p ^ r ∣ choose n k * k :=
if hn0 : n = 0 then by cases k; simp [hn0, choose_zero_succ, lt_irrefl, *] at *
else
begin
  have := le_multiplicity_choose hp (nat.pos_of_ne_zero hn0) hk0 hkn,
  rw [← hp.multiplicity_mul, multiplicity_le_multiplicity_iff] at this,
  simp only [nat.pow_eq_pow] at this,
  exact this r hpn
end

lemma zmod.is_unit_iff_coprime (n : ℕ+) (a : ℕ) :
  is_unit (a : zmod n) ↔ coprime a n :=
have hc : coprime a n ↔ coprime (a : zmod n).val n,
  by rw [zmod.val_cast_nat, coprime, coprime, ← gcd_rec, nat.gcd_comm],
⟨λ ⟨u, hu⟩, begin
  have : coprime (u : zmod n).val n:= (@zmod.units_equiv_coprime n u).2,
  rwa [← hu, ← hc] at this,
end, λ h, ⟨(@zmod.units_equiv_coprime n).symm ⟨a, hc.1 h⟩, rfl⟩⟩

lemma nat.prime.pow_dvd_of_dvd_mul_of_not_dvd {p r m n : ℕ} (hp : p.prime) (hdvd : p ^ r ∣ m * n)
  (hpn : ¬p ∣ n) : p ^ r ∣ m :=
begin
  induction r with r ih,
  { simp },
  { cases ih (dvd_trans ⟨p, nat.pow_succ _ _⟩ hdvd) with a ha,
    rw [ha, mul_assoc, nat.pow_succ, nat.mul_dvd_mul_iff_left (nat.pow_pos hp.pos _),
      hp.dvd_mul] at hdvd,
    rw [ha, nat.pow_succ, nat.mul_dvd_mul_iff_left (nat.pow_pos hp.pos _)],
    tauto }
end

lemma dvd_of_forall_prime_pow_dvd : ∀ {m n : ℕ} (h : ∀ (p r : ℕ), p.prime → p ^ r ∣ m → p ^ r ∣ n), m ∣ n
| 0     n h :=
  by_contradiction (λ hn0,
    have hn0 : 0 < n, from nat.pos_of_ne_zero (mt zero_dvd_iff.2 hn0),
    not_le_of_gt (lt_pow_self (show 1 < 2, from dec_trivial) n) (le_of_dvd hn0 (h _ _ prime_two (dvd_zero _))))
| 1     n h := one_dvd _
| (m+2) n h :=
let p := min_fac (m+2) in
have hp : p.prime, from min_fac_prime dec_trivial,
have wf : (m + 2) / p < m + 2, from factors_lemma,
have hpn : p ∣ n, by rw [← nat.pow_one p]; exact h _ _ hp (by convert min_fac_dvd _; simp),
have (m + 2) / p ∣ n / p, from dvd_of_forall_prime_pow_dvd
  (λ q r hq (hdvd : q ^ r ∣ (m + 2) / p), show q ^ r ∣ n / p,
    from if hpq : p = q then begin
      subst hpq,
      have : p ^ (r + 1) ∣ n, from h p (r+1) hp
        (by rw [← nat.div_mul_cancel (min_fac_dvd (m+2)), nat.pow_succ];
          exact mul_dvd_mul hdvd (dvd_refl _)),
      have hpn : p ∣ n, from dvd_trans (by simp [nat.pow_succ]) this,
      rwa [← nat.mul_dvd_mul_iff_left hp.pos, nat.mul_div_cancel' hpn, mul_comm, ← nat.pow_succ],
    end
    else begin
      have := h q r hq (dvd_trans hdvd (div_dvd_of_dvd (min_fac_dvd _))),
      rw [← nat.div_mul_cancel hpn] at this,
      refine hq.pow_dvd_of_dvd_mul_of_not_dvd this _,
      simp [nat.dvd_prime hp, ne.symm hpq, ne_of_gt hq.one_lt],
    end),
by rw [← nat.mul_div_cancel' hpn, ← nat.mul_div_cancel' (min_fac_dvd (m + 2))];
  exact mul_dvd_mul (dvd_refl _) this

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
#print nat.lt_pow_self
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