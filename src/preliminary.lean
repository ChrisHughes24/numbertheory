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
