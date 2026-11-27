import Meat.Open.Interference
import Meat.Channel.MultipleAccessKAchievability
import Meat.Shannon.ChainRule
import Meat.Open.Broadcast
import Meat.Open.Interactive

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Meat

namespace IC

universe u

@[instance_reducible]
private def optionMeasurableSpace (α : Type*) : MeasurableSpace (Option α) := ⊤

attribute [local instance] optionMeasurableSpace

private lemma optionMeasurableSingletonClass (α : Type*) :
    MeasurableSingletonClass (Option α) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

attribute [local instance] optionMeasurableSingletonClass

section Triple

private def tri {F : Fin 3 → Sort*} (a : F 0) (b : F 1) (c : F 2) : ∀ k, F k :=
  Fin.cons a (Fin.cons b (Fin.cons c finZeroElim))

private def triAlph (X Y Z : Type u) : Fin 3 → Type u := ![X, Y, Z]

variable {X Y Z : Type u}

private instance triFintype [Fintype X] [Fintype Y] [Fintype Z] : ∀ k, Fintype (triAlph X Y Z k) :=
  tri (F := fun k => Fintype (triAlph X Y Z k)) (inferInstanceAs (Fintype X))
    (inferInstanceAs (Fintype Y)) (inferInstanceAs (Fintype Z))

private instance triDecEq [DecidableEq X] [DecidableEq Y] [DecidableEq Z] :
    ∀ k, DecidableEq (triAlph X Y Z k) :=
  tri (F := fun k => DecidableEq (triAlph X Y Z k)) (inferInstanceAs (DecidableEq X))
    (inferInstanceAs (DecidableEq Y)) (inferInstanceAs (DecidableEq Z))

private instance triMeas [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] :
    ∀ k, MeasurableSpace (triAlph X Y Z k) :=
  tri (F := fun k => MeasurableSpace (triAlph X Y Z k)) (inferInstanceAs (MeasurableSpace X))
    (inferInstanceAs (MeasurableSpace Y)) (inferInstanceAs (MeasurableSpace Z))

private instance triMSC [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y] [MeasurableSingletonClass Z] :
    ∀ k, MeasurableSingletonClass (triAlph X Y Z k) :=
  tri (F := fun k => MeasurableSingletonClass (triAlph X Y Z k))
    (inferInstanceAs (MeasurableSingletonClass X)) (inferInstanceAs (MeasurableSingletonClass Y))
    (inferInstanceAs (MeasurableSingletonClass Z))

end Triple

section TriSum

private lemma sum_tri {F : Fin 3 → Type*} [∀ k, Fintype (F k)] (f : (∀ k, F k) → ℝ) :
    ∑ C : ∀ k, F k, f C = ∑ a : F 0, ∑ b : F 1, ∑ c : F 2, f (tri a b c) := by
  rw [← (Fin.consEquiv F).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  rw [← (Fin.consEquiv fun i : Fin 2 => F i.succ).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun b _ => ?_
  rw [← (Fin.consEquiv fun i : Fin 1 => F i.succ.succ).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_unique]
  congr 1

end TriSum

section Receiver

variable {U P U' P' A A' B : Type u} [Fintype U] [Fintype P] [Fintype U']
  [Fintype P'] [Fintype B]

private noncomputable def rxChannel (Z : DMC (A × A') B) (pP' : PMF P') (f : U → P → A)
    (f' : U' → P' → A') :
    DMC (∀ k, triAlph U P U' k) B :=
  fun a => pP'.bind fun t => Z (f (a 0) (a 1), f' (a 2) t)

private noncomputable def rxLaw (pU : PMF U) (pP : PMF P) (pU' : PMF U') :
    ∀ k, PMF (triAlph U P U' k) :=
  tri (F := fun k => PMF (triAlph U P U' k)) pU pP pU'

omit [Fintype U] [Fintype P] [Fintype U'] [Fintype B] in
private lemma sum_iidProb_mul_blockProb_rx {n : ℕ} (Z : DMC (A × A') B) (pP' : PMF P')
    (f : U → P → A)
    (f' : U' → P' → A')
    (a : Fin n → ∀ k, triAlph U P U' k) (y : Fin n → B) :
    ∑ t : Fin n → P', iidProb (pP') t *
        (DMC.blockProb Z (fun i => (f (a i 0) (a i 1), f' (a i 2) (t i))) y).toReal =
      (DMC.blockProb (rxChannel Z pP' f f') a y).toReal := by
  simp only [iidProb, DMC.blockProb, ENNReal.toReal_prod, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (t : P') => (pP' t).toReal *
    (Z (f (a i 0) (a i 1), f' (a i 2) t) (y i)).toReal)]
  refine prod_congr rfl fun i _ => ?_
  rw [rxChannel, PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum fun t _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  simp only [ENNReal.toReal_mul]

end Receiver

section ReceiverBound

variable {U P U' P' A A' B : Type u} [Fintype U] [Fintype P] [Fintype U']
  [Fintype P'] [Fintype B]

omit [Fintype U] [Fintype P] [Fintype U'] in
private lemma sum_rxError_le {n : ℕ} {L : Fin 3 → ℕ} {M' : Type*} [Fintype M'] [DecidableEq M']
    (Z : DMC (A × A') B) (pP' : PMF P') (f : U → P → A)
    (f' : U' → P' → A')
    (C : ∀ k, Fin (L k) → Fin n → triAlph U P U' k)
    (D : Finset ((Fin n → ∀ k, triAlph U P U' k) × (Fin n → B))) (m₀ m : ∀ k, Fin (L k))
    (m' : M') :
    ∑ d : M' → Fin n → P', (∏ j, iidProb (pP') (d j)) *
      ∑ y, (if ((MACKCode.typicalCode C D m₀).dec y 0, (MACKCode.typicalCode C D m₀).dec y 1) =
          (m 0, m 1) then 0 else 1) *
        (DMC.blockProb Z (fun i => (f (C 0 (m 0) i) (C 1 (m 1) i), f' (C 2 (m 2) i) (d m' i)))
          y).toReal ≤
      ((MACKCode.typicalCode C D m₀).errorProb (rxChannel Z pP' f f') m).toReal := by
  set dec := (MACKCode.typicalCode C D m₀).dec
  calc _ = ∑ y, (if (dec y 0, dec y 1) = (m 0, m 1) then 0 else 1) *
        (DMC.blockProb (rxChannel Z pP' f f') (MACK.codeInput C m) y).toReal := by
        rw [sum_prod_mul_apply (fun _ x => iidProb (pP') x)
          (fun _ => sum_iidProb _ n) (fun t => ∑ y, (if (dec y 0, dec y 1) = (m 0, m 1) then 0
            else 1) * (DMC.blockProb Z (fun i => (f (C 0 (m 0) i) (C 1 (m 1) i),
              f' (C 2 (m 2) i) (t i))) y).toReal) m']
        simp only [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun y _ => ?_
        rw [← sum_iidProb_mul_blockProb_rx Z pP' f f' (MACK.codeInput C m) y, mul_sum]
        exact sum_congr rfl fun t _ => by rw [mul_left_comm]; rfl
    _ ≤ _ := by
        rw [MACKCode.errorProb, ENNReal.toReal_sum fun y _ => by
          split_ifs <;> simp [DMC.blockProb_ne_top]]
        refine sum_le_sum fun y _ => ?_
        by_cases h : dec y = m
        · have h' : (dec y 0, dec y 1) = (m 0, m 1) := by rw [h]
          simp [h']
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
          refine mul_le_of_le_one_left ENNReal.toReal_nonneg ?_
          split_ifs <;> norm_num

end ReceiverBound

section ReceiverSum

variable {U P U' P' A A' B : Type u} [Fintype U] [Fintype P] [Fintype U']
  [Fintype P'] [Fintype B]

private noncomputable def rxErr {n : ℕ} {L : Fin 3 → ℕ} {M' : Type*} (Z : DMC (A × A') B)
    (f : U → P → A) (f' : U' → P' → A')
    (C : ∀ k, Fin (L k) → Fin n → triAlph U P U' k)
    (D : Finset ((Fin n → ∀ k, triAlph U P U' k) × (Fin n → B))) (m₀ m : ∀ k, Fin (L k))
    (m' : M') (d : M' → Fin n → P') : ℝ :=
  ∑ y, (if ((MACKCode.typicalCode C D m₀).dec y 0, (MACKCode.typicalCode C D m₀).dec y 1) =
      (m 0, m 1) then 0 else 1) *
    (DMC.blockProb Z (fun i => (f (C 0 (m 0) i) (C 1 (m 1) i), f' (C 2 (m 2) i) (d m' i))) y).toReal

omit [Fintype U] [Fintype P] [Fintype U'] [Fintype P'] in
private lemma rxErr_nonneg {n : ℕ} {L : Fin 3 → ℕ} {M' : Type*} (Z : DMC (A × A') B)
    (f : U → P → A) (f' : U' → P' → A')
    (C : ∀ k, Fin (L k) → Fin n → triAlph U P U' k)
    (D : Finset ((Fin n → ∀ k, triAlph U P U' k) × (Fin n → B))) (m₀ m : ∀ k, Fin (L k))
    (m' : M') (d : M' → Fin n → P') : 0 ≤ rxErr Z f f' C D m₀ m m' d :=
  sum_nonneg fun y _ => mul_nonneg (by split_ifs <;> norm_num) ENNReal.toReal_nonneg

variable [MeasurableSpace U] [MeasurableSpace P] [MeasurableSpace U'] [MeasurableSpace B]

private lemma sum_rx_le {n : ℕ} {L : Fin 3 → ℕ} {M' : Type*} [Fintype M'] [DecidableEq M']
    (Z : DMC (A × A') B) (pU : PMF U) (pP : PMF P) (pU' : PMF U') (pP' : PMF P')
    (f : U → P → A) (f' : U' → P' → A')
    (ε : ℝ) (m₀ m : ∀ k, Fin (L k)) (m' : M') :
    ∑ a : Fin (L 0) → Fin n → triAlph U P U' 0,
      ∑ b : Fin (L 1) → Fin n → triAlph U P U' 1,
      ∑ c : Fin (L 2) → Fin n → triAlph U P U' 2,
      ∑ d : M' → Fin n → P',
        (∏ j, iidProb (rxLaw pU pP pU' 0) (a j)) * (∏ j, iidProb (rxLaw pU pP pU' 1) (b j)) *
          (∏ j, iidProb (rxLaw pU pP pU' 2) (c j)) *
          (∏ j, iidProb (pP') (d j)) *
          rxErr Z f f' (tri (F := fun k => Fin (L k) → Fin n → triAlph U P U' k) a b c)
            (MACK.decodingSet (rxChannel Z pP' f f') (rxLaw pU pP pU') n ε) m₀ m m' d ≤
      (1 - ∑ xy ∈ MACK.decodingSet (rxChannel Z pP' f f') (rxLaw pU pP pU') n ε,
          iidProb (DMC.jointPMF (rxChannel Z pP' f f') (piPMF (rxLaw pU pP pU')))
            (fun i => (xy.1 i, xy.2 i))) +
        ∑ S ∈ univ.erase (∅ : Finset (Fin 3)), (∏ k ∈ S, ((Fintype.card (Fin (L k)) : ℝ) - 1)) *
          Real.exp (-(n * ((MACK.sideChannel (rxChannel Z pP' f f') (rxLaw pU pP pU')
            S).inputMutualInfo
            (piPMF fun k : {k // k ∈ S} => rxLaw pU pP pU' k) - 3 * ε))) := by
  set ρ := rxLaw pU pP pU'
  set D := MACK.decodingSet (rxChannel Z pP' f f') ρ n ε
  set F := fun k => Fin (L k) → Fin n → triAlph U P U' k
  have hcw : ∀ (a : F 0) (b : F 1) (c : F 2), MACK.codebookWeight ρ (tri (F := F) a b c) =
      (∏ j, iidProb (ρ 0) (a j)) * (∏ j, iidProb (ρ 1) (b j)) * (∏ j, iidProb (ρ 2) (c j)) :=
    fun a b c => by
      rw [MACK.codebookWeight, Fin.prod_univ_three]
      rfl
  calc _ = ∑ a : F 0, ∑ b : F 1, ∑ c : F 2, MACK.codebookWeight ρ (tri (F := F) a b c) *
        ∑ d : M' → Fin n → P', (∏ j, iidProb (pP') (d j)) *
          rxErr Z f f' (tri (F := F) a b c) D m₀ m m' d := by
        refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
        rw [hcw, mul_sum]
        exact sum_congr rfl fun d _ => by ring
    _ ≤ ∑ a : F 0, ∑ b : F 1, ∑ c : F 2, MACK.codebookWeight ρ (tri (F := F) a b c) *
        ((MACKCode.typicalCode (tri (F := F) a b c) D m₀).errorProb (rxChannel Z pP' f f')
          m).toReal :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (sum_rxError_le Z pP' f f' _ D m₀ m m')
            (prod_nonneg fun k _ => prod_nonneg fun j _ => iidProb_nonneg _ _)
    _ = ∑ C : ∀ k, F k, MACK.codebookWeight ρ C *
        ((MACKCode.typicalCode C D m₀).errorProb (rxChannel Z pP' f f') m).toReal :=
        (sum_tri (F := F) fun C => MACK.codebookWeight ρ C *
          ((MACKCode.typicalCode C D m₀).errorProb (rxChannel Z pP' f f') m).toReal).symm
    _ ≤ _ := MACK.sum_errorProb_typicalCode_le (rxChannel Z pP' f f') ρ ε m₀ m

end ReceiverSum

section Error

variable {A₁ A₂ B₁ B₂ : Type*} [Fintype B₁] [Fintype B₂]

private lemma errorProb_le_add' {M₁ M₂ : Type*} [DecidableEq M₁] [DecidableEq M₂] {n : ℕ}
    (c : ICCode M₁ M₂ A₁ A₂ B₁ B₂ n) (W : DMC (A₁ × A₂) (B₁ × B₂)) (m : M₁ × M₂) :
    (c.errorProb W m).toReal ≤
      ∑ y₁, (if c.dec₁ y₁ = m.1 then 0 else 1) *
        (DMC.blockProb (out₁ W) (fun i => (c.enc₁ m.1 i, c.enc₂ m.2 i)) y₁).toReal +
      ∑ y₂, (if c.dec₂ y₂ = m.2 then 0 else 1) *
        (DMC.blockProb (out₂ W) (fun i => (c.enc₁ m.1 i, c.enc₂ m.2 i)) y₂).toReal := by
  set x : Fin n → A₁ × A₂ := fun i => (c.enc₁ m.1 i, c.enc₂ m.2 i)
  have h : c.errorProb W m ≤
      ∑ y₁, (if c.dec₁ y₁ = m.1 then 0 else 1) * DMC.blockProb (out₁ W) x y₁ +
      ∑ y₂, (if c.dec₂ y₂ = m.2 then 0 else 1) * DMC.blockProb (out₂ W) x y₂ := by
    rw [← sum_mul_blockProb_out₁ W x (fun y₁ => if c.dec₁ y₁ = m.1 then 0 else 1),
      ← sum_mul_blockProb_out₂ W x (fun y₂ => if c.dec₂ y₂ = m.2 then 0 else 1),
      ← sum_add_distrib, ICCode.errorProb]
    refine sum_le_sum fun y _ => ?_
    by_cases a : c.dec₁ (fun i => (y i).1) = m.1 <;> by_cases b : c.dec₂ (fun i => (y i).2) = m.2
    · have : (c.dec₁ (fun i => (y i).1), c.dec₂ (fun i => (y i).2)) = m := Prod.ext a b
      rw [ite_eq_left_of_eq_true _ _ (eq_true this)]
      exact zero_le
    · have : (c.dec₁ (fun i => (y i).1), c.dec₂ (fun i => (y i).2)) ≠ m :=
        fun h => b (congrArg Prod.snd h)
      rw [ite_eq_right_of_eq_false _ _ (eq_false this)]
      simp [a, b, x]
    · have : (c.dec₁ (fun i => (y i).1), c.dec₂ (fun i => (y i).2)) ≠ m :=
        fun h => a (congrArg Prod.fst h)
      rw [ite_eq_right_of_eq_false _ _ (eq_false this)]
      simp [a, b, x]
    · have : (c.dec₁ (fun i => (y i).1), c.dec₂ (fun i => (y i).2)) ≠ m :=
        fun h => a (congrArg Prod.fst h)
      rw [ite_eq_right_of_eq_false _ _ (eq_false this)]
      simp only [a, b, ite_false, one_mul]
      exact le_self_add (b := DMC.blockProb W x y)
  refine (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun y _ =>
    ENNReal.mul_ne_top (by split_ifs <;> simp) (DMC.blockProb_ne_top _ _ _),
    ENNReal.sum_ne_top.2 fun y _ =>
    ENNReal.mul_ne_top (by split_ifs <;> simp) (DMC.blockProb_ne_top _ _ _)⟩) h).trans_eq ?_
  rw [ENNReal.toReal_add (ENNReal.sum_ne_top.2 fun y _ =>
    ENNReal.mul_ne_top (by split_ifs <;> simp) (DMC.blockProb_ne_top _ _ _))
    (ENNReal.sum_ne_top.2 fun y _ =>
    ENNReal.mul_ne_top (by split_ifs <;> simp) (DMC.blockProb_ne_top _ _ _)),
    ENNReal.toReal_sum fun y _ =>
      ENNReal.mul_ne_top (by split_ifs <;> simp) (DMC.blockProb_ne_top _ _ _),
    ENNReal.toReal_sum fun y _ =>
      ENNReal.mul_ne_top (by split_ifs <;> simp) (DMC.blockProb_ne_top _ _ _)]
  simp only [ENNReal.toReal_mul, apply_ite ENNReal.toReal, ENNReal.toReal_zero,
    ENNReal.toReal_one]

end Error

section Code

variable {A₁ A₂ B₁ B₂ V₁ V₂ P₁ P₂ : Type u} [Fintype B₁] [Fintype B₂]
  [Fintype V₁] [Fintype V₂] [Fintype P₁] [Fintype P₂]

private def rxL (a b c : ℕ) : Fin 3 → ℕ := ![a, b, c]

private def book {U T U' : Type u} {n a b c : ℕ} (CU : Fin a → Fin n → U) (CT : Fin b → Fin n → T)
    (CU' : Fin c → Fin n → U') : ∀ k, Fin (rxL a b c k) → Fin n → triAlph U T U' k :=
  tri (F := fun k => Fin (rxL a b c k) → Fin n → triAlph U T U' k) CU CT CU'

private def msg {a b c : ℕ} (x : Fin a) (y : Fin b) (z : Fin c) : ∀ k, Fin (rxL a b c k) :=
  tri (F := fun k => Fin (rxL a b c k)) x y z

private noncomputable def hkCode {n l₁₀ l₁₁ l₂₀ l₂₁ : ℕ} (f₁ : V₁ → P₁ → A₁)
    (f₂ : V₂ → P₂ → A₂)
    (CU₁ : Fin l₁₀ → Fin n → V₁) (CT₁ : Fin l₁₁ → Fin n → P₁)
    (CU₂ : Fin l₂₀ → Fin n → V₂) (CT₂ : Fin l₂₁ → Fin n → P₂)
    (D₁ : Finset ((Fin n → ∀ k, triAlph V₁ P₁ V₂ k) × (Fin n → B₁)))
    (D₂ : Finset ((Fin n → ∀ k, triAlph V₂ P₂ V₁ k) × (Fin n → B₂)))
    (m₁ : ∀ k, Fin (rxL l₁₀ l₁₁ l₂₀ k)) (m₂ : ∀ k, Fin (rxL l₂₀ l₂₁ l₁₀ k)) :
    ICCode (Fin l₁₀ × Fin l₁₁) (Fin l₂₀ × Fin l₂₁) A₁ A₂ B₁ B₂ n where
  enc₁ m i := f₁ (CU₁ m.1 i) (CT₁ m.2 i)
  enc₂ m i := f₂ (CU₂ m.1 i) (CT₂ m.2 i)
  dec₁ y := ((MACKCode.typicalCode (book CU₁ CT₁ CU₂) D₁ m₁).dec y 0,
    (MACKCode.typicalCode (book CU₁ CT₁ CU₂) D₁ m₁).dec y 1)
  dec₂ y := ((MACKCode.typicalCode (book CU₂ CT₂ CU₁) D₂ m₂).dec y 0,
    (MACKCode.typicalCode (book CU₂ CT₂ CU₁) D₂ m₂).dec y 1)

omit [Fintype V₁] [Fintype V₂] [Fintype P₁] [Fintype P₂] in
private lemma errorProb_hkCode_le {n l₁₀ l₁₁ l₂₀ l₂₁ : ℕ} (f₁ : V₁ → P₁ → A₁)
    (f₂ : V₂ → P₂ → A₂)
    (CU₁ : Fin l₁₀ → Fin n → V₁) (CT₁ : Fin l₁₁ → Fin n → P₁)
    (CU₂ : Fin l₂₀ → Fin n → V₂) (CT₂ : Fin l₂₁ → Fin n → P₂)
    (D₁ : Finset ((Fin n → ∀ k, triAlph V₁ P₁ V₂ k) × (Fin n → B₁)))
    (D₂ : Finset ((Fin n → ∀ k, triAlph V₂ P₂ V₁ k) × (Fin n → B₂)))
    (m₁ : ∀ k, Fin (rxL l₁₀ l₁₁ l₂₀ k)) (m₂ : ∀ k, Fin (rxL l₂₀ l₂₁ l₁₀ k))
    (W : DMC (A₁ × A₂) (B₁ × B₂)) (m : (Fin l₁₀ × Fin l₁₁) × (Fin l₂₀ × Fin l₂₁)) :
    ((hkCode f₁ f₂ CU₁ CT₁ CU₂ CT₂ D₁ D₂ m₁ m₂).errorProb W m).toReal ≤
      rxErr (out₁ W) f₁ f₂ (book CU₁ CT₁ CU₂) D₁ m₁ (msg m.1.1 m.1.2 m.2.1) m.2.2 CT₂ +
        rxErr (fun a => out₂ W a.swap) f₂ f₁ (book CU₂ CT₂ CU₁) D₂ m₂ (msg m.2.1 m.2.2 m.1.1) m.1.2
          CT₁ :=
  errorProb_le_add' _ W m

end Code

section Total

private lemma sum4_comm {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d :=
        sum_congr rfl fun a _ => by
          rw [sum_comm]
          exact sum_congr rfl fun c _ => sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := sum_comm
    _ = _ := sum_congr rfl fun c _ => sum_comm

variable {A₁ A₂ B₁ B₂ V₁ V₂ P₁ P₂ : Type u} [Fintype B₁] [Fintype B₂]
  [Fintype V₁] [Fintype V₂] [Fintype P₁] [Fintype P₂]
  [MeasurableSpace B₁] [MeasurableSpace B₂]
  [MeasurableSpace V₁] [MeasurableSpace V₂] [MeasurableSpace P₁]
  [MeasurableSpace P₂]

private noncomputable def rxBound {U P U' P' A A' B : Type u} [Fintype U] [Fintype P]
    [Fintype U'] [Fintype B] [MeasurableSpace U] [MeasurableSpace P]
    [MeasurableSpace U'] [MeasurableSpace B] (Z : DMC (A × A') B) (pU : PMF U) (pP : PMF P)
    (pU' : PMF U') (pP' : PMF P') (f : U → P → A) (f' : U' → P' → A') (n : ℕ) (ε : ℝ)
    (L : Fin 3 → ℕ) : ℝ :=
  (1 - ∑ xy ∈ MACK.decodingSet (rxChannel Z pP' f f') (rxLaw pU pP pU') n ε,
      iidProb (DMC.jointPMF (rxChannel Z pP' f f') (piPMF (rxLaw pU pP pU')))
        (fun i => (xy.1 i, xy.2 i))) +
    ∑ S ∈ univ.erase (∅ : Finset (Fin 3)), (∏ k ∈ S, ((Fintype.card (Fin (L k)) : ℝ) - 1)) *
      Real.exp (-(n * ((MACK.sideChannel (rxChannel Z pP' f f') (rxLaw pU pP pU')
            S).inputMutualInfo
        (piPMF fun k : {k // k ∈ S} => rxLaw pU pP pU' k) - 3 * ε)))

private lemma sum_hk_le {n l₁₀ l₁₁ l₂₀ l₂₁ : ℕ} (W : DMC (A₁ × A₂) (B₁ × B₂)) (pU₁ : PMF V₁)
    (pP₁ : PMF P₁) (pU₂ : PMF V₂) (pP₂ : PMF P₂)
    (f₁ : V₁ → P₁ → A₁) (f₂ : V₂ → P₂ → A₂) (ε : ℝ)
    (m₁ : ∀ k, Fin (rxL l₁₀ l₁₁ l₂₀ k)) (m₂ : ∀ k, Fin (rxL l₂₀ l₂₁ l₁₀ k))
    (m : (Fin l₁₀ × Fin l₁₁) × (Fin l₂₀ × Fin l₂₁)) :
    ∑ CU₁ : Fin l₁₀ → Fin n → V₁, ∑ CT₁ : Fin l₁₁ → Fin n → P₁,
      ∑ CU₂ : Fin l₂₀ → Fin n → V₂, ∑ CT₂ : Fin l₂₁ → Fin n → P₂,
        (∏ j, iidProb pU₁ (CU₁ j)) * (∏ j, iidProb pP₁ (CT₁ j)) *
          (∏ j, iidProb pU₂ (CU₂ j)) * (∏ j, iidProb pP₂ (CT₂ j)) *
          ((hkCode f₁ f₂ CU₁ CT₁ CU₂ CT₂
            (MACK.decodingSet (rxChannel (out₁ W) pP₂ f₁ f₂) (rxLaw pU₁ pP₁ pU₂) n ε)
            (MACK.decodingSet (rxChannel (fun a => out₂ W a.swap) pP₁ f₂ f₁)
              (rxLaw pU₂ pP₂ pU₁) n ε)
            m₁ m₂).errorProb W m).toReal ≤
      rxBound (out₁ W) pU₁ pP₁ pU₂ pP₂ f₁ f₂ n ε (rxL l₁₀ l₁₁ l₂₀) +
        rxBound (fun a => out₂ W a.swap) pU₂ pP₂ pU₁ pP₁ f₂ f₁ n ε (rxL l₂₀ l₂₁ l₁₀) := by
  set D₁ := MACK.decodingSet (rxChannel (out₁ W) pP₂ f₁ f₂) (rxLaw pU₁ pP₁ pU₂) n ε
  set D₂ := MACK.decodingSet (rxChannel (fun a => out₂ W a.swap) pP₁ f₂ f₁) (rxLaw pU₂ pP₂ pU₁) n ε
  have hw : ∀ (CU₁ : Fin l₁₀ → Fin n → V₁) (CT₁ : Fin l₁₁ → Fin n → P₁)
      (CU₂ : Fin l₂₀ → Fin n → V₂) (CT₂ : Fin l₂₁ → Fin n → P₂),
      0 ≤ (∏ j, iidProb pU₁ (CU₁ j)) * (∏ j, iidProb pP₁ (CT₁ j)) *
          (∏ j, iidProb pU₂ (CU₂ j)) * (∏ j, iidProb pP₂ (CT₂ j)) :=
    fun _ _ _ _ => by
      have := fun {S : Type u} [Fintype S] (p : PMF S) {k : ℕ} (C : Fin k → Fin n → S) =>
        prod_nonneg fun j (_ : j ∈ univ) => iidProb_nonneg p (C j)
      exact mul_nonneg (mul_nonneg (mul_nonneg (this _ _) (this _ _)) (this _ _)) (this _ _)
  have h₁ := sum_rx_le (n := n) (out₁ W) pU₁ pP₁ pU₂ pP₂ f₁ f₂ ε m₁ (msg m.1.1 m.1.2 m.2.1) m.2.2
  have h₂ := sum_rx_le (n := n) (fun a => out₂ W a.swap) pU₂ pP₂ pU₁ pP₁ f₂ f₁ ε m₂
    (msg m.2.1 m.2.2 m.1.1) m.1.2
  calc _ ≤ ∑ CU₁ : Fin l₁₀ → Fin n → V₁, ∑ CT₁ : Fin l₁₁ → Fin n → P₁,
      ∑ CU₂ : Fin l₂₀ → Fin n → V₂, ∑ CT₂ : Fin l₂₁ → Fin n → P₂,
        (∏ j, iidProb pU₁ (CU₁ j)) * (∏ j, iidProb pP₁ (CT₁ j)) *
          (∏ j, iidProb pU₂ (CU₂ j)) * (∏ j, iidProb pP₂ (CT₂ j)) *
          (rxErr (out₁ W) f₁ f₂ (book CU₁ CT₁ CU₂) D₁ m₁ (msg m.1.1 m.1.2 m.2.1) m.2.2 CT₂ +
            rxErr (fun a => out₂ W a.swap) f₂ f₁ (book CU₂ CT₂ CU₁) D₂ m₂ (msg m.2.1 m.2.2 m.1.1)
              m.1.2 CT₁) :=
        sum_le_sum fun CU₁ _ => sum_le_sum fun CT₁ _ => sum_le_sum fun CU₂ _ =>
          sum_le_sum fun CT₂ _ => mul_le_mul_of_nonneg_left
            (errorProb_hkCode_le f₁ f₂ CU₁ CT₁ CU₂ CT₂ D₁ D₂ m₁ m₂ W m) (hw CU₁ CT₁ CU₂ CT₂)
    _ = (∑ CU₁ : Fin l₁₀ → Fin n → V₁, ∑ CT₁ : Fin l₁₁ → Fin n → P₁,
      ∑ CU₂ : Fin l₂₀ → Fin n → V₂, ∑ CT₂ : Fin l₂₁ → Fin n → P₂,
        (∏ j, iidProb pU₁ (CU₁ j)) * (∏ j, iidProb pP₁ (CT₁ j)) *
          (∏ j, iidProb pU₂ (CU₂ j)) * (∏ j, iidProb pP₂ (CT₂ j)) *
          rxErr (out₁ W) f₁ f₂ (book CU₁ CT₁ CU₂) D₁ m₁ (msg m.1.1 m.1.2 m.2.1) m.2.2 CT₂) +
      ∑ CU₂ : Fin l₂₀ → Fin n → V₂, ∑ CT₂ : Fin l₂₁ → Fin n → P₂,
      ∑ CU₁ : Fin l₁₀ → Fin n → V₁, ∑ CT₁ : Fin l₁₁ → Fin n → P₁,
        (∏ j, iidProb pU₂ (CU₂ j)) * (∏ j, iidProb pP₂ (CT₂ j)) *
          (∏ j, iidProb pU₁ (CU₁ j)) * (∏ j, iidProb pP₁ (CT₁ j)) *
          rxErr (fun a => out₂ W a.swap) f₂ f₁ (book CU₂ CT₂ CU₁) D₂ m₂ (msg m.2.1 m.2.2 m.1.1)
            m.1.2 CT₁ := by
        simp only [mul_add, sum_add_distrib]
        congr 1
        rw [sum4_comm]
        refine sum_congr rfl fun CU₂ _ => sum_congr rfl fun CT₂ _ =>
          sum_congr rfl fun CU₁ _ => sum_congr rfl fun CT₁ _ => ?_
        ring
    _ ≤ _ := add_le_add h₁ h₂

end Total

section Achievable

variable {A₁ A₂ B₁ B₂ V₁ V₂ P₁ P₂ : Type u} [Fintype B₁] [Fintype B₂]
  [Fintype V₁] [Fintype V₂] [Fintype P₁] [Fintype P₂]
  [MeasurableSpace B₁] [MeasurableSpace B₂]
  [MeasurableSpace V₁] [MeasurableSpace V₂] [MeasurableSpace P₁]
  [MeasurableSpace P₂]
  [MeasurableSingletonClass B₁] [MeasurableSingletonClass B₂] [MeasurableSingletonClass V₁]
  [MeasurableSingletonClass V₂]
  [MeasurableSingletonClass P₁] [MeasurableSingletonClass P₂]

private lemma mul_exp_le' {n : ℕ} {x R I I' η : ℝ} (hx : x ≤ Real.exp (n * R)) (hI : I ≤ I')
    (hη : 4 * η ≤ I - R) : x * Real.exp (-(n * (I' - 3 * η))) ≤ Real.exp (n * (-η)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc x * Real.exp (-(n * (I' - 3 * η))) ≤ Real.exp (n * R) * Real.exp (-(n * (I - 3 * η))) :=
        mul_le_mul hx (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (n * R - n * (I - 3 * η)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (n * (-η)) := Real.exp_le_exp.2 (by nlinarith)

private lemma rxBound_le {U P U' P' A A' B : Type u} [Fintype U] [Fintype P]
    [Fintype U'] [Fintype B] [MeasurableSpace U]
    [MeasurableSpace P] [MeasurableSpace U'] [MeasurableSpace B] [MeasurableSingletonClass U]
    [MeasurableSingletonClass P] [MeasurableSingletonClass U'] [MeasurableSingletonClass B]
    (Z : DMC (A × A') B) (pU : PMF U) (pP : PMF P) (pU' : PMF U') (pP' : PMF P')
    (f : U → P → A) (f' : U' → P' → A')
    {n : ℕ} {η : ℝ} {L : Fin 3 → ℕ} {r : Fin 3 → ℝ}
    (hL : ∀ k, (L k : ℝ) - 1 ≤ Real.exp (n * r k)) (hL0 : ∀ k, (0 : ℝ) ≤ L k - 1)
    (hη : ∀ S ∈ univ.erase (∅ : Finset (Fin 3)),
      4 * η ≤ MACK.subsetInfo (rxChannel Z pP' f f') (rxLaw pU pP pU') S - ∑ k ∈ S, r k) :
    rxBound Z pU pP pU' pP' f f' n η L ≤
      (1 - ∑ xy ∈ MACK.decodingSet (rxChannel Z pP' f f') (rxLaw pU pP pU') n η,
        iidProb (DMC.jointPMF (rxChannel Z pP' f f') (piPMF (rxLaw pU pP pU')))
          (fun i => (xy.1 i, xy.2 i))) +
        ((univ.erase (∅ : Finset (Fin 3))).card : ℝ) * Real.exp (n * (-η)) := by
  have hS : ∀ S ∈ univ.erase (∅ : Finset (Fin 3)),
      (∏ k ∈ S, ((Fintype.card (Fin (L k)) : ℝ) - 1)) *
        Real.exp (-(n * ((MACK.sideChannel (rxChannel Z pP' f f') (rxLaw pU pP pU')
            S).inputMutualInfo
          (piPMF fun k : {k // k ∈ S} => rxLaw pU pP pU' k) - 3 * η))) ≤ Real.exp (n * (-η)) := by
    intro S hS
    refine mul_exp_le' ?_ (MACK.subsetInfo_le_inputMutualInfo _ _ S) (hη S hS)
    rw [mul_sum, Real.exp_sum]
    exact prod_le_prod₀ (fun k _ => by rw [Fintype.card_fin]; exact hL0 k)
      fun k _ => by rw [Fintype.card_fin]; exact hL k
  have := sum_le_sum hS
  rw [sum_const, nsmul_eq_mul] at this
  unfold rxBound
  linarith

private lemma tendsto_rx {U P U' P' A A' B : Type u} [Fintype U] [Fintype P]
    [Fintype U'] [Fintype B] [MeasurableSpace U]
    [MeasurableSpace P] [MeasurableSpace U'] [MeasurableSpace B] [MeasurableSingletonClass U]
    [MeasurableSingletonClass P] [MeasurableSingletonClass U'] [MeasurableSingletonClass B]
    (Z : DMC (A × A') B) (pU : PMF U) (pP : PMF P) (pU' : PMF U') (pP' : PMF P')
    (f : U → P → A) (f' : U' → P' → A')
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => (1 - ∑ xy ∈ MACK.decodingSet (rxChannel Z pP' f f') (rxLaw pU pP pU') n η,
        iidProb (DMC.jointPMF (rxChannel Z pP' f f') (piPMF (rxLaw pU pP pU')))
          (fun i => (xy.1 i, xy.2 i))) +
        ((univ.erase (∅ : Finset (Fin 3))).card : ℝ) * Real.exp (n * (-η))) atTop (𝓝 0) := by
  have h1 := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (MACK.tendsto_sum_iidProb_decodingSet (rxChannel Z pP' f f') (rxLaw pU pP pU') hη)
  simpa using h1.add ((tendsto_exp_nat_mul (neg_neg_of_pos hη)).const_mul
    ((univ.erase (∅ : Finset (Fin 3))).card : ℝ))

end Achievable

section Main

variable {A₁ A₂ B₁ B₂ V₁ V₂ P₁ P₂ : Type u} [Fintype B₁] [Fintype B₂]
  [Fintype V₁] [Fintype V₂] [Fintype P₁] [Fintype P₂]
  [MeasurableSpace B₁] [MeasurableSpace B₂]
  [MeasurableSpace V₁] [MeasurableSpace V₂] [MeasurableSpace P₁]
  [MeasurableSpace P₂]
  [MeasurableSingletonClass B₁] [MeasurableSingletonClass B₂] [MeasurableSingletonClass V₁]
  [MeasurableSingletonClass V₂]
  [MeasurableSingletonClass P₁] [MeasurableSingletonClass P₂]

private lemma sum_codebook_eq_one {S : Type u} [Fintype S] (p : PMF S) (k n : ℕ) :
    ∑ C : Fin k → Fin n → S, ∏ j, iidProb p (C j) = 1 :=
  sum_prod (fun _ x => iidProb p x) (fun _ => sum_iidProb p n)

private lemma achievable_of_lt_split (W : DMC (A₁ × A₂) (B₁ × B₂)) (pU₁ : PMF V₁)
    (pP₁ : PMF P₁) (pU₂ : PMF V₂) (pP₂ : PMF P₂)
    (f₁ : V₁ → P₁ → A₁) (f₂ : V₂ → P₂ → A₂) {R₁₀ R₁₁ R₂₀ R₂₁ : ℝ}
    (h₁ : ∀ S : Finset (Fin 3), S.Nonempty → ∑ k ∈ S, ![R₁₀, R₁₁, R₂₀] k <
      MACK.subsetInfo (rxChannel (out₁ W) pP₂ f₁ f₂) (rxLaw pU₁ pP₁ pU₂) S)
    (h₂ : ∀ S : Finset (Fin 3), S.Nonempty → ∑ k ∈ S, ![R₂₀, R₂₁, R₁₀] k <
      MACK.subsetInfo (rxChannel (fun a => out₂ W a.swap) pP₁ f₂ f₁) (rxLaw pU₂ pP₂ pU₁) S) :
    Achievable W (R₁₀ + R₁₁) (R₂₀ + R₂₁) := by
  classical
  set I₁ := fun S => MACK.subsetInfo (rxChannel (out₁ W) pP₂ f₁ f₂) (rxLaw pU₁ pP₁ pU₂) S
  set I₂ := fun S =>
    MACK.subsetInfo (rxChannel (fun a => out₂ W a.swap) pP₁ f₂ f₁) (rxLaw pU₂ pP₂ pU₁) S
  set r₁ : Fin 3 → ℝ := ![R₁₀, R₁₁, R₂₀]
  set r₂ : Fin 3 → ℝ := ![R₂₀, R₂₁, R₁₀]
  intro ε hε
  obtain ⟨δ, -, hδ0, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδ0
  set g : Finset (Fin 3) → ℝ := fun S =>
    if S = ∅ then 1 else min (I₁ S - ∑ k ∈ S, r₁ k) (I₂ S - ∑ k ∈ S, r₂ k)
  set η := univ.inf' univ_nonempty g / 4 with hη
  have hη0 : 0 < η := by
    refine div_pos ((lt_inf'_iff _).2 fun S _ => ?_) (by norm_num)
    by_cases hS : S = ∅
    · simp [g, hS]
    · simp only [g, hS, ite_false]
      exact lt_min (by linarith [h₁ S (nonempty_iff_ne_empty.2 hS)])
        (by linarith [h₂ S (nonempty_iff_ne_empty.2 hS)])
  have hη₁ : ∀ S ∈ univ.erase (∅ : Finset (Fin 3)), 4 * η ≤ I₁ S - ∑ k ∈ S, r₁ k := by
    intro S hS
    have := inf'_le g (mem_univ S)
    simp only [g, ne_of_mem_erase hS, ite_false] at this
    rw [hη]
    linarith [min_le_left (I₁ S - ∑ k ∈ S, r₁ k) (I₂ S - ∑ k ∈ S, r₂ k)]
  have hη₂ : ∀ S ∈ univ.erase (∅ : Finset (Fin 3)), 4 * η ≤ I₂ S - ∑ k ∈ S, r₂ k := by
    intro S hS
    have := inf'_le g (mem_univ S)
    simp only [g, ne_of_mem_erase hS, ite_false] at this
    rw [hη]
    linarith [min_le_right (I₁ S - ∑ k ∈ S, r₁ k) (I₂ S - ∑ k ∈ S, r₂ k)]
  have hsum := (tendsto_rx (out₁ W) pU₁ pP₁ pU₂ pP₂ f₁ f₂ hη0).add
    (tendsto_rx (fun a => out₂ W a.swap) pU₂ pP₂ pU₁ pP₁ f₂ f₁ hη0)
  rw [add_zero] at hsum
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hsum.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn => ?_⟩
  set l : ℝ → ℕ := fun R => ⌈Real.exp (n * R)⌉₊
  have hl : ∀ R, 0 < l R := fun R => Nat.ceil_pos.2 (Real.exp_pos _)
  have hl' : ∀ R, (l R : ℝ) - 1 ≤ Real.exp (n * R) := fun R => by
    linarith [Nat.ceil_lt_add_one (Real.exp_pos (n * R)).le]
  have hl0 : ∀ R, (0 : ℝ) ≤ l R - 1 := fun R => by
    have : (1 : ℝ) ≤ l R := Nat.one_le_cast.2 (hl R)
    linarith
  have hle : ∀ R, Real.exp (n * R) ≤ l R := fun R => Nat.le_ceil _
  have : NeZero (l R₁₀) := ⟨(hl R₁₀).ne'⟩
  have : NeZero (l R₁₁) := ⟨(hl R₁₁).ne'⟩
  have : NeZero (l R₂₀) := ⟨(hl R₂₀).ne'⟩
  have : NeZero (l R₂₁) := ⟨(hl R₂₁).ne'⟩
  have hL₁ : ∀ k, ((rxL (l R₁₀) (l R₁₁) (l R₂₀) k : ℕ) : ℝ) - 1 ≤ Real.exp (n * r₁ k) := by
    intro k
    fin_cases k
    · exact hl' R₁₀
    · exact hl' R₁₁
    · exact hl' R₂₀
  have hL₁0 : ∀ k, (0 : ℝ) ≤ (rxL (l R₁₀) (l R₁₁) (l R₂₀) k : ℕ) - 1 := by
    intro k
    fin_cases k
    · exact hl0 R₁₀
    · exact hl0 R₁₁
    · exact hl0 R₂₀
  have hL₂ : ∀ k, ((rxL (l R₂₀) (l R₂₁) (l R₁₀) k : ℕ) : ℝ) - 1 ≤ Real.exp (n * r₂ k) := by
    intro k
    fin_cases k
    · exact hl' R₂₀
    · exact hl' R₂₁
    · exact hl' R₁₀
  have hL₂0 : ∀ k, (0 : ℝ) ≤ (rxL (l R₂₀) (l R₂₁) (l R₁₀) k : ℕ) - 1 := by
    intro k
    fin_cases k
    · exact hl0 R₂₀
    · exact hl0 R₂₁
    · exact hl0 R₁₀
  have hb₁ := rxBound_le (out₁ W) pU₁ pP₁ pU₂ pP₂ f₁ f₂ hL₁ hL₁0 hη₁ (n := n)
  have hb₂ := rxBound_le (fun a => out₂ W a.swap) pU₂ pP₂ pU₁ pP₁ f₂ f₁ hL₂ hL₂0 hη₂ (n := n)
  set β := rxBound (out₁ W) pU₁ pP₁ pU₂ pP₂ f₁ f₂ n η (rxL (l R₁₀) (l R₁₁) (l R₂₀)) +
    rxBound (fun a => out₂ W a.swap) pU₂ pP₂ pU₁ pP₁ f₂ f₁ n η (rxL (l R₂₀) (l R₂₁) (l R₁₀))
  have hβ : β < δ := by linarith [hN n hn]
  set D₁ := MACK.decodingSet (rxChannel (out₁ W) pP₂ f₁ f₂) (rxLaw pU₁ pP₁ pU₂) n η
  set D₂ := MACK.decodingSet (rxChannel (fun a => out₂ W a.swap) pP₁ f₂ f₁) (rxLaw pU₂ pP₂ pU₁) n η
  set m₁ : ∀ k, Fin (rxL (l R₁₀) (l R₁₁) (l R₂₀) k) := msg 0 0 0
  set m₂ : ∀ k, Fin (rxL (l R₂₀) (l R₂₁) (l R₁₀) k) := msg 0 0 0
  set w : ((Fin (l R₁₀) → Fin n → V₁) × ((Fin (l R₁₁) → Fin n → P₁) ×
    ((Fin (l R₂₀) → Fin n → V₂) × (Fin (l R₂₁) → Fin n → P₂)))) → ℝ :=
    fun G => (∏ j, iidProb pU₁ (G.1 j)) *
    (∏ j, iidProb pP₁ (G.2.1 j)) * (∏ j, iidProb pU₂ (G.2.2.1 j)) *
    (∏ j, iidProb pP₂ (G.2.2.2 j))
  set code : ((Fin (l R₁₀) → Fin n → V₁) × ((Fin (l R₁₁) → Fin n → P₁) ×
    ((Fin (l R₂₀) → Fin n → V₂) × (Fin (l R₂₁) → Fin n → P₂)))) →
    ICCode (Fin (l R₁₀) × Fin (l R₁₁)) (Fin (l R₂₀) × Fin (l R₂₁)) A₁ A₂ B₁ B₂ n :=
    fun G => hkCode f₁ f₂ G.1 G.2.1 G.2.2.1 G.2.2.2 D₁ D₂ m₁ m₂
  have hw : ∀ G, 0 ≤ w G := fun G => by
    have := fun {S : Type u} [Fintype S] (p : PMF S) {k : ℕ} (C : Fin k → Fin n → S) =>
      prod_nonneg fun j (_ : j ∈ univ) => iidProb_nonneg p (C j)
    exact mul_nonneg (mul_nonneg (mul_nonneg (this _ _) (this _ _)) (this _ _)) (this _ _)
  have h1 : ∑ G, w G = 1 := by
    simp only [w, Fintype.sum_prod_type, ← mul_sum, sum_codebook_eq_one, mul_one]
  have hm : ∀ m, ∑ G, w G * ((code G).errorProb W m).toReal ≤ β := fun m => by
    simp only [w, code, Fintype.sum_prod_type]
    exact sum_hk_le (n := n) W pU₁ pP₁ pU₂ pP₂ f₁ f₂ η m₁ m₂ m
  obtain ⟨G, hG⟩ := exists_le_of_sum_mul_le (w := w)
    (f := fun G => ∑ m, ((code G).errorProb W m).toReal)
    (t := Fintype.card ((Fin (l R₁₀) × Fin (l R₁₁)) × (Fin (l R₂₀) × Fin (l R₂₁))) * β) hw h1 (by
      simp only [mul_sum]
      rw [sum_comm]
      calc _ ≤ ∑ m : (Fin (l R₁₀) × Fin (l R₁₁)) × (Fin (l R₂₀) × Fin (l R₂₁)), β :=
            sum_le_sum fun m _ => hm m
        _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul])
  have hc : (code G).avgError W ≤ ENNReal.ofReal β := by
    rw [← ICCode.avgError_toMACCode, ← MACCode.avgError_toBlockCode]
    exact BlockCode.avgError_le_ofReal _ W hG
  refine ⟨l R₁₀ * l R₁₁, l R₂₀ * l R₂₁, ?_, ?_,
    (code G).relabel finProdFinEquiv finProdFinEquiv, ?_⟩
  · rw [mul_add, Real.exp_add, Nat.cast_mul]
    exact mul_le_mul (hle R₁₀) (hle R₁₁) (Real.exp_pos _).le (Nat.cast_nonneg _)
  · rw [mul_add, Real.exp_add, Nat.cast_mul]
    exact mul_le_mul (hle R₂₀) (hle R₂₁) (Real.exp_pos _).le (Nat.cast_nonneg _)
  · rw [← ICCode.avgError_toMACCode, ICCode.toMACCode_relabel, MACCode.avgError_relabel,
      ICCode.avgError_toMACCode]
    exact hc.trans ((ENNReal.ofReal_le_ofReal hβ.le).trans hδε.le)

end Main

section Relabel

variable {Ω S S' T U U' : Type*} [MeasurableSpace Ω]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype S'] [MeasurableSpace S'] [MeasurableSingletonClass S']
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype U'] [MeasurableSpace U'] [MeasurableSingletonClass U'] (μ : Measure Ω)

private lemma condMutualInfo_relabel {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {g : S → S'}
    {h : U → U'} (hg : Function.Injective g) (hh : Function.Injective h) :
    I[fun ω => g (X ω) : Y | fun ω => h (Z ω) ; μ] = I[X : Y | Z ; μ] := by
  rw [condMutualInfo_def, condMutualInfo_def,
    condEntropy_cond_of_injective μ (X := fun ω => g (X ω)) hh fun ω => rfl,
    condEntropy_cond_of_injective μ (X := Y) hh fun ω => rfl,
    condEntropy_cond_of_injective μ (X := fun ω => (g (X ω), Y ω)) hh fun ω => rfl]
  have e1 : H[fun ω => g (X ω) | Z ; μ] = H[X | Z ; μ] :=
    condEntropy_comp_of_injective μ (X := X) hg
  have e2 : H[fun ω => (g (X ω), Y ω) | Z ; μ] = H[fun ω => (X ω, Y ω) | Z ; μ] :=
    condEntropy_comp_of_injective μ (X := fun ω => (X ω, Y ω)) (f := fun p => (g p.1, p.2))
      fun a b hab => by
        simp only [Prod.mk.injEq] at hab
        exact Prod.ext (hg hab.1) hab.2
  rw [e1, e2]

end Relabel

section Law


variable {U P U' P' A A' B : Type u}

noncomputable def hkLaw [MeasurableSpace U] [MeasurableSpace P] [MeasurableSpace U']
    [MeasurableSpace B] (Z : DMC (A × A') B) (pU : PMF U) (pP : PMF P) (pU' : PMF U')
    (pP' : PMF P') (f : U → P → A) (f' : U' → P' → A') : Measure (U × P × U' × B) :=
  (DMC.jointPMF (fun u => DMC.jointPMF (fun p => DMC.jointPMF
    (fun u' => pP'.bind fun p' => Z (f u p, f' u' p')) pU') pP) pU).toMeasure

def selectThree (S : Finset (Fin 3)) (x : U × P × U') : Option U × Option P × Option U' :=
  (if 0 ∈ S then some x.1 else none, if 1 ∈ S then some x.2.1 else none,
    if 2 ∈ S then some x.2.2 else none)

variable [Fintype U] [Fintype P] [Fintype U'] [Fintype P'] [Fintype B]
  [MeasurableSpace U] [MeasurableSpace P] [MeasurableSpace U'] [MeasurableSpace B]
  [MeasurableSingletonClass U] [MeasurableSingletonClass P] [MeasurableSingletonClass U']
  [MeasurableSingletonClass B]

private def triOut (ω : (∀ k, triAlph U P U' k) × B) : U × P × U' × B :=
  (ω.1 0, ω.1 1, ω.1 2, ω.2)

omit [Fintype U] [Fintype P] [Fintype U'] [Fintype B] [MeasurableSpace U] [MeasurableSpace P]
  [MeasurableSpace U'] [MeasurableSpace B] [MeasurableSingletonClass U]
  [MeasurableSingletonClass P] [MeasurableSingletonClass U'] [MeasurableSingletonClass B] in
private lemma triOut_injective :
    Function.Injective (triOut (U := U) (P := P) (U' := U') (B := B)) := by
  intro a b h
  obtain ⟨h0, h'⟩ := Prod.mk.inj h
  obtain ⟨h1, h''⟩ := Prod.mk.inj h'
  obtain ⟨h2, h3⟩ := Prod.mk.inj h''
  refine Prod.ext (funext fun k => ?_) h3
  fin_cases k
  · exact h0
  · exact h1
  · exact h2

omit [Fintype P'] [Fintype B] in
private lemma map_jointMeasure_rx [Finite B] (Z : DMC (A × A') B) (pU : PMF U) (pP : PMF P)
    (pU' : PMF U')
    (pP' : PMF P') (f : U → P → A) (f' : U' → P' → A') :
    ((rxChannel Z pP' f f').jointMeasure (piPMF (rxLaw pU pP pU'))).map triOut =
      hkLaw Z pU pP pU' pP' f f' := by
  have := Fintype.ofFinite B
  rw [DMC.jointMeasure_eq_toMeasure, PMF.toMeasure_map _ _ (measurable_of_finite _), hkLaw]
  congr 1
  ext ⟨u, p, u', y⟩
  have e : ((u, p, u', y) : U × P × U' × B) =
      triOut (tri (F := fun k => triAlph U P U' k) u p u', y) := rfl
  rw [e, PMF.map_apply_of_injective _ triOut_injective, DMC.jointPMF_apply, piPMF_apply,
    Fin.prod_univ_three]
  rw [← e]
  simp only [DMC.jointPMF_apply]
  rw [mul_assoc, mul_assoc]
  rfl

omit [Fintype P'] in
private lemma subsetInfo_eq (Z : DMC (A × A') B) (pU : PMF U) (pP : PMF P) (pU' : PMF U')
    (pP' : PMF P') (f : U → P → A) (f' : U' → P' → A') (S : Finset (Fin 3)) :
    MACK.subsetInfo (rxChannel Z pP' f f') (rxLaw pU pP pU') S =
      I[fun ω : U × P × U' × B => selectThree S (ω.1, ω.2.1, ω.2.2.1) : fun ω => ω.2.2.2 |
        fun ω => selectThree Sᶜ (ω.1, ω.2.1, ω.2.2.1) ; hkLaw Z pU pP pU' pP' f f'] := by
  rw [← map_jointMeasure_rx, condMutualInfo_map _ (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
  set g : MACK.Masked (triAlph U P U') → Option U × Option P × Option U' :=
    fun m => (m 0, m 1, m 2)
  have hg : Function.Injective g := by
    intro a b h
    obtain ⟨h0, h'⟩ := Prod.mk.inj h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    funext k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
  have h := condMutualInfo_relabel ((rxChannel Z pP' f f').jointMeasure (piPMF (rxLaw pU pP pU')))
    (X := fun ω : (∀ k, triAlph U P U' k) × B => MACK.mask S ω.1) (Y := Prod.snd)
    (Z := fun ω => MACK.mask Sᶜ ω.1) hg hg
  rw [MACK.subsetInfo, ← h]
  rfl

end Law

section Region

variable {A₁ A₂ B₁ B₂ V₁ V₂ P₁ P₂ : Type u} [Fintype B₁] [Fintype B₂]
  [Fintype V₁] [Fintype V₂] [Fintype P₁] [Fintype P₂]
  [MeasurableSpace B₁] [MeasurableSpace B₂]
  [MeasurableSpace V₁] [MeasurableSpace V₂] [MeasurableSpace P₁] [MeasurableSpace P₂]
  [MeasurableSingletonClass B₁] [MeasurableSingletonClass B₂] [MeasurableSingletonClass V₁]
  [MeasurableSingletonClass V₂]
  [MeasurableSingletonClass P₁] [MeasurableSingletonClass P₂]

noncomputable def hanKobayashi1981Region (W : DMC (A₁ × A₂) (B₁ × B₂)) (pU₁ : PMF V₁)
    (pP₁ : PMF P₁) (pU₂ : PMF V₂) (pP₂ : PMF P₂) (f₁ : V₁ → P₁ → A₁) (f₂ : V₂ → P₂ → A₂) :
    Set (ℝ × ℝ) :=
  {R | ∃ r₁₀ r₁₁ r₂₀ r₂₁ : ℝ, 0 ≤ r₁₀ ∧ 0 ≤ r₁₁ ∧ 0 ≤ r₂₀ ∧ 0 ≤ r₂₁ ∧
    R.1 = r₁₀ + r₁₁ ∧ R.2 = r₂₀ + r₂₁ ∧ ∀ S : Finset (Fin 3),
      ∑ k ∈ S, ![r₁₀, r₁₁, r₂₀] k ≤
        I[fun ω : V₁ × P₁ × V₂ × B₁ => selectThree S (ω.1, ω.2.1, ω.2.2.1) :
          fun ω => ω.2.2.2 | fun ω => selectThree Sᶜ (ω.1, ω.2.1, ω.2.2.1) ;
          hkLaw (out₁ W) pU₁ pP₁ pU₂ pP₂ f₁ f₂] ∧
      ∑ k ∈ S, ![r₂₀, r₂₁, r₁₀] k ≤
        I[fun ω : V₂ × P₂ × V₁ × B₂ => selectThree S (ω.1, ω.2.1, ω.2.2.1) :
          fun ω => ω.2.2.2 | fun ω => selectThree Sᶜ (ω.1, ω.2.1, ω.2.2.1) ;
          hkLaw (fun a => out₂ W a.swap) pU₂ pP₂ pU₁ pP₁ f₂ f₁]}

private lemma sum_sub_half {x y z t : ℝ} (S : Finset (Fin 3)) :
    ∑ k ∈ S, ![x - t, y - t, z - t] k = ∑ k ∈ S, ![x, y, z] k - S.card * t := by
  have e : ∀ k, ![x - t, y - t, z - t] k = ![x, y, z] k - t := by
    intro k
    fin_cases k <;> rfl
  rw [sum_congr rfl fun k _ => e k, sum_sub_distrib, sum_const, nsmul_eq_mul]

theorem hanKobayashi1981Region_subset_closure_achievableRegion (W : DMC (A₁ × A₂) (B₁ × B₂))
    (pU₁ : PMF V₁) (pP₁ : PMF P₁) (pU₂ : PMF V₂) (pP₂ : PMF P₂) (f₁ : V₁ → P₁ → A₁)
    (f₂ : V₂ → P₂ → A₂) :
    hanKobayashi1981Region W pU₁ pP₁ pU₂ pP₂ f₁ f₂ ⊆ closure (achievableRegion W) := by
  rintro R ⟨a, b, c, d, ha, hb, hc, hd, h1, h2, hS⟩
  refine mem_closure_achievableRegion W (by rw [h1]; positivity) (by rw [h2]; positivity)
    fun δ hδ => ?_
  have hlt : ∀ (S : Finset (Fin 3)), S.Nonempty → ∀ {x y z I : ℝ},
      ∑ k ∈ S, ![x, y, z] k ≤ I → ∑ k ∈ S, ![x - δ / 2, y - δ / 2, z - δ / 2] k < I := by
    intro S hne x y z I h
    have hc : (0 : ℝ) < S.card := Nat.cast_pos.2 (card_pos.2 hne)
    rw [sum_sub_half]
    nlinarith
  have key := achievable_of_lt_split W pU₁ pP₁ pU₂ pP₂ f₁ f₂
    (R₁₀ := a - δ / 2) (R₁₁ := b - δ / 2) (R₂₀ := c - δ / 2) (R₂₁ := d - δ / 2)
    (fun S hne => by rw [subsetInfo_eq]; exact hlt S hne (hS S).1)
    (fun S hne => by rw [subsetInfo_eq]; exact hlt S hne (hS S).2)
  have e1 : R.1 - δ = a - δ / 2 + (b - δ / 2) := by rw [h1]; ring
  have e2 : R.2 - δ = c - δ / 2 + (d - δ / 2) := by rw [h2]; ring
  rw [e1, e2]
  exact key

end Region

section Union

private instance uliftFinMSC (k : ℕ) : MeasurableSingletonClass (ULift.{u} (Fin k)) :=
  ⟨fun _ => MeasurableSet.of_discrete⟩

variable {A₁ A₂ B₁ B₂ : Type u} [Fintype B₁] [Fintype B₂]
  [MeasurableSpace B₁] [MeasurableSpace B₂]
  [MeasurableSingletonClass B₁] [MeasurableSingletonClass B₂]

noncomputable def hanKobayashi1981Union (W : DMC (A₁ × A₂) (B₁ × B₂)) : Set (ℝ × ℝ) :=
  closure (convexHull ℝ (⋃ (k : ℕ) (pU₁ : PMF (ULift.{u} (Fin k)))
    (pP₁ : PMF (ULift.{u} (Fin k))) (pU₂ : PMF (ULift.{u} (Fin k)))
    (pP₂ : PMF (ULift.{u} (Fin k))) (f₁ : ULift.{u} (Fin k) → ULift.{u} (Fin k) → A₁)
    (f₂ : ULift.{u} (Fin k) → ULift.{u} (Fin k) → A₂),
    hanKobayashi1981Region W pU₁ pP₁ pU₂ pP₂ f₁ f₂))

theorem hanKobayashi1981Union_subset_closure_achievableRegion (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    hanKobayashi1981Union W ⊆ closure (achievableRegion W) :=
  closure_minimal (convexHull_min (Set.iUnion_subset fun _ => Set.iUnion_subset fun _ =>
    Set.iUnion_subset fun _ => Set.iUnion_subset fun _ => Set.iUnion_subset fun _ =>
      Set.iUnion_subset fun _ => Set.iUnion_subset fun _ =>
        hanKobayashi1981Region_subset_closure_achievableRegion W _ _ _ _ _ _)
    (convex_closure_achievableRegion W)) isClosed_closure

end Union

section Generic

variable {U P U' P' A A' B : Type u} [Fintype U] [Fintype P] [Fintype U'] [Fintype A]
  [Fintype B]
  [MeasurableSpace U] [MeasurableSpace P] [MeasurableSpace U'] [MeasurableSpace A]
  [MeasurableSpace B] [MeasurableSingletonClass U] [MeasurableSingletonClass P]
  [MeasurableSingletonClass U'] [MeasurableSingletonClass A] [MeasurableSingletonClass B]

omit [Fintype A] [Fintype B] [Fintype P] [Fintype U'] [Fintype U] [MeasurableSingletonClass A]
  [MeasurableSingletonClass B] [MeasurableSingletonClass P] [MeasurableSingletonClass U']
  [MeasurableSingletonClass U] [MeasurableSpace A] in
private lemma isProbabilityMeasure_hkLaw (Z : DMC (A × A') B) (pU : PMF U) (pP : PMF P)
    (pU' : PMF U') (pP' : PMF P') (f : U → P → A) (f' : U' → P' → A') :
    IsProbabilityMeasure (hkLaw Z pU pP pU' pP' f f') := by
  unfold hkLaw
  infer_instance

omit [Fintype A] [Fintype B] [Fintype P] [Fintype U'] [Fintype U] in
omit [MeasurableSingletonClass A] [MeasurableSpace A] in
private lemma hkLaw_kernel [Finite U'] [Finite U] [Finite B] [Finite A] [Finite P] (Z : DMC (A × A')
    B) (pU : PMF U) (pP : PMF P) (pU' : PMF U')
    (pP' : PMF P') (f : U → P → A) (f' : U' → P' → A') (t : U × P × U') (b : B) :
    (hkLaw Z pU pP pU' pP' f f').real
        {ω | (ω.1, ω.2.1, ω.2.2.1) = t ∧ ω.2.2.2 = b} =
      (hkLaw Z pU pP pU' pP' f f').real {ω | (ω.1, ω.2.1, ω.2.2.1) = t} *
        ((fun x : A × U' => pP'.bind fun p' => Z (x.1, f' x.2 p')) (f t.1 t.2.1, t.2.2)
          b).toReal := by
  have := Fintype.ofFinite U'
  have := Fintype.ofFinite U
  have := Fintype.ofFinite B
  have := Fintype.ofFinite A
  have := Fintype.ofFinite P
  have := isProbabilityMeasure_hkLaw Z pU pP pU' pP' f f'
  have hpt : ∀ b' : B, (hkLaw Z pU pP pU' pP' f f').real
      {ω | (ω.1, ω.2.1, ω.2.2.1) = t ∧ ω.2.2.2 = b'} =
        (pU t.1).toReal * ((pP t.2.1).toReal * ((pU' t.2.2).toReal *
          ((pP'.bind fun p' => Z (f t.1 t.2.1, f' t.2.2 p')) b').toReal)) := by
    intro b'
    have e : {ω : U × P × U' × B | (ω.1, ω.2.1, ω.2.2.1) = t ∧ ω.2.2.2 = b'} =
        {(t.1, t.2.1, t.2.2, b')} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.ext_iff]
      tauto
    rw [e, measureReal_def, hkLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      DMC.jointPMF_apply, DMC.jointPMF_apply, DMC.jointPMF_apply]
    simp only [ENNReal.toReal_mul]
  have hs := sum_measureReal_inter (μ := hkLaw Z pU pP pU' pP' f f')
    (X := fun ω : U × P × U' × B => ω.2.2.2) (measurable_of_finite _)
    {ω | (ω.1, ω.2.1, ω.2.2.1) = t}
  have e2 : ∀ b', (hkLaw Z pU pP pU' pP' f f').real
      {ω | ω.2.2.2 = b' ∧ ω ∈ {ω : U × P × U' × B | (ω.1, ω.2.1, ω.2.2.1) = t}} =
        (hkLaw Z pU pP pU' pP' f f').real {ω | (ω.1, ω.2.1, ω.2.2.1) = t ∧ ω.2.2.2 = b'} :=
    fun b' => by
      congr 1
      ext ω
      simp only [Set.mem_ofPred_eq]
      tauto
  simp only [e2, hpt] at hs
  rw [← hs, hpt]
  have h1 : ∑ b', ((pP'.bind fun p' => Z (f t.1 t.2.1, f' t.2.2 p')) b').toReal = 1 := by
    rw [← ENNReal.toReal_sum fun _ _ => PMF.apply_ne_top _ _, sum_pmf_eq_one, ENNReal.toReal_one]
  simp only [← mul_sum, h1, mul_one]
  ring

private lemma condEntropy_full (Z : DMC (A × A') B) (pU : PMF U) (pP : PMF P) (pU' : PMF U')
    (pP' : PMF P') (f : U → P → A) (f' : U' → P' → A') :
    H[fun ω : U × P × U' × B => ω.2.2.2 | fun ω => (ω.1, ω.2.1, ω.2.2.1) ;
        hkLaw Z pU pP pU' pP' f f'] =
      H[fun ω : U × P × U' × B => ω.2.2.2 | fun ω => (f ω.1 ω.2.1, ω.2.2.1) ;
        hkLaw Z pU pP pU' pP' f f'] := by
  have := isProbabilityMeasure_hkLaw Z pU pP pU' pP' f f'
  exact Interactive.condEntropy_eq_comp_of_kernel _ (measurable_of_finite _)
    (measurable_of_finite _) (fun t : U × P × U' => (f t.1 t.2.1, t.2.2))
    (fun x : A × U' => pP'.bind fun p' => Z (x.1, f' x.2 p'))
    (hkLaw_kernel Z pU pP pU' pP' f f')

end Generic

section Mine

variable {U P U' P' A A' B : Type u} [Fintype U] [Fintype P] [Fintype U'] [Fintype A]
  [Fintype B]
  [MeasurableSpace U] [MeasurableSpace P] [MeasurableSpace U'] [MeasurableSpace A]
  [MeasurableSpace B] [MeasurableSingletonClass U] [MeasurableSingletonClass P]
  [MeasurableSingletonClass U'] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
  (Z : DMC (A × A') B) (pU : PMF U) (pP : PMF P) (pU' : PMF U') (pP' : PMF P')
  (f : U → P → A) (f' : U' → P' → A')

omit [Fintype P] in
private lemma condEntropy_mid [Finite P] :
    H[fun ω : U × P × U' × B => ω.2.2.2 | fun ω => (ω.1, f ω.1 ω.2.1, ω.2.2.1) ;
        hkLaw Z pU pP pU' pP' f f'] =
      H[fun ω : U × P × U' × B => ω.2.2.2 | fun ω => (f ω.1 ω.2.1, ω.2.2.1) ;
        hkLaw Z pU pP pU' pP' f f'] := by
  have := Fintype.ofFinite P
  have := isProbabilityMeasure_hkLaw Z pU pP pU' pP' f f'
  have h1 := condEntropy_le_condEntropy_comp (μ := hkLaw Z pU pP pU' pP' f f')
    (X := fun ω : U × P × U' × B => ω.2.2.2) (Y := fun ω => (ω.1, ω.2.1, ω.2.2.1))
    (measurable_of_finite _) (measurable_of_finite _) (fun t => (t.1, f t.1 t.2.1, t.2.2))
  have h2 := condEntropy_le_condEntropy_comp (μ := hkLaw Z pU pP pU' pP' f f')
    (X := fun ω : U × P × U' × B => ω.2.2.2) (Y := fun ω => (ω.1, f ω.1 ω.2.1, ω.2.2.1))
    (measurable_of_finite _) (measurable_of_finite _) (fun t => (t.2.1, t.2.2))
  have h3 := condEntropy_full Z pU pP pU' pP' f f'
  have e1 : ((fun t : U × P × U' => (t.1, f t.1 t.2.1, t.2.2)) ∘
      fun ω : U × P × U' × B => (ω.1, ω.2.1, ω.2.2.1)) =
      fun ω => (ω.1, f ω.1 ω.2.1, ω.2.2.1) := rfl
  have e2 : ((fun t : U × A × U' => (t.2.1, t.2.2)) ∘
      fun ω : U × P × U' × B => (ω.1, f ω.1 ω.2.1, ω.2.2.1)) =
      fun ω => (f ω.1 ω.2.1, ω.2.2.1) := rfl
  rw [e1] at h1
  rw [e2] at h2
  linarith

private lemma condEntropy_sel_full (S : Finset (Fin 3)) :
    H[fun ω : U × P × U' × B => ω.2.2.2 | fun ω => (selectThree S (ω.1, ω.2.1, ω.2.2.1),
        selectThree Sᶜ (ω.1, ω.2.1, ω.2.2.1)) ; hkLaw Z pU pP pU' pP' f f'] =
      H[fun ω : U × P × U' × B => ω.2.2.2 | fun ω => (f ω.1 ω.2.1, ω.2.2.1) ;
        hkLaw Z pU pP pU' pP' f f'] := by
  rw [← condEntropy_full Z pU pP pU' pP' f f']
  refine condEntropy_cond_of_injective _
    (e := fun t : U × P × U' => (selectThree S t, selectThree Sᶜ t)) ?_ fun ω => rfl
  intro a b h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  simp only [selectThree, Prod.mk.injEq] at h1 h2
  have k0 : a.1 = b.1 := by
    by_cases hs : (0 : Fin 3) ∈ S
    · simpa [hs] using h1.1
    · have : (0 : Fin 3) ∈ Sᶜ := mem_compl.2 hs
      simpa [this] using h2.1
  have k1 : a.2.1 = b.2.1 := by
    by_cases hs : (1 : Fin 3) ∈ S
    · simpa [hs] using h1.2.1
    · have : (1 : Fin 3) ∈ Sᶜ := mem_compl.2 hs
      simpa [this] using h2.2.1
  have k2 : a.2.2 = b.2.2 := by
    by_cases hs : (2 : Fin 3) ∈ S
    · simpa [hs] using h1.2.2
    · have : (2 : Fin 3) ∈ Sᶜ := mem_compl.2 hs
      simpa [this] using h2.2.2
  exact Prod.ext k0 (Prod.ext k1 k2)

end Mine

section Mine2

variable {U P U' P' A A' B : Type u} [Fintype U] [Fintype P] [Fintype U'] [Fintype A]
  [Fintype B]
  [MeasurableSpace U] [MeasurableSpace P] [MeasurableSpace U'] [MeasurableSpace A]
  [MeasurableSpace B] [MeasurableSingletonClass U] [MeasurableSingletonClass P]
  [MeasurableSingletonClass U'] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
  (Z : DMC (A × A') B) (pU : PMF U) (pP : PMF P) (pU' : PMF U') (pP' : PMF P')
  (f : U → P → A) (f' : U' → P' → A')

private lemma sel_info (S : Finset (Fin 3)) :
    I[fun ω : U × P × U' × B => selectThree S (ω.1, ω.2.1, ω.2.2.1) : fun ω => ω.2.2.2 |
        fun ω => selectThree Sᶜ (ω.1, ω.2.1, ω.2.2.1) ; hkLaw Z pU pP pU' pP' f f'] =
      H[fun ω : U × P × U' × B => ω.2.2.2 | fun ω => selectThree Sᶜ (ω.1, ω.2.1, ω.2.2.1) ;
        hkLaw Z pU pP pU' pP' f f'] -
      H[fun ω : U × P × U' × B => ω.2.2.2 | fun ω => (f ω.1 ω.2.1, ω.2.2.1) ;
        hkLaw Z pU pP pU' pP' f f'] := by
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy, condEntropy_sel_full]

private lemma sel_info₀₁ :
    I[fun ω : U × P × U' × B => selectThree {0, 1} (ω.1, ω.2.1, ω.2.2.1) : fun ω => ω.2.2.2 |
        fun ω => selectThree {0, 1}ᶜ (ω.1, ω.2.1, ω.2.2.1) ; hkLaw Z pU pP pU' pP' f f'] =
      H[fun ω : U × P × U' × B => ω.2.2.2 | fun ω => ω.2.2.1 ; hkLaw Z pU pP pU' pP' f f'] -
      H[fun ω : U × P × U' × B => ω.2.2.2 | fun ω => (f ω.1 ω.2.1, ω.2.2.1) ;
        hkLaw Z pU pP pU' pP' f f'] := by
  rw [sel_info]
  congr 1
  exact condEntropy_cond_of_injective _ (e := fun v : U' => ((none : Option U), (none : Option P),
    some v)) (fun a b h => by simpa using h) fun ω => by simp [selectThree]

private lemma sel_info_univ :
    I[fun ω : U × P × U' × B => selectThree univ (ω.1, ω.2.1, ω.2.2.1) : fun ω => ω.2.2.2 |
        fun ω => selectThree univᶜ (ω.1, ω.2.1, ω.2.2.1) ; hkLaw Z pU pP pU' pP' f f'] =
      H[fun ω : U × P × U' × B => ω.2.2.2 | fun _ => () ; hkLaw Z pU pP pU' pP' f f'] -
      H[fun ω : U × P × U' × B => ω.2.2.2 | fun ω => (f ω.1 ω.2.1, ω.2.2.1) ;
        hkLaw Z pU pP pU' pP' f f'] := by
  rw [sel_info]
  congr 1
  exact condEntropy_cond_of_injective _ (e := fun _ : Unit => ((none : Option U),
    (none : Option P), (none : Option U'))) (fun a b _ => rfl) fun ω => by simp [selectThree]

private lemma sel_info₁ :
    I[fun ω : U × P × U' × B => selectThree {1} (ω.1, ω.2.1, ω.2.2.1) : fun ω => ω.2.2.2 |
        fun ω => selectThree {1}ᶜ (ω.1, ω.2.1, ω.2.2.1) ; hkLaw Z pU pP pU' pP' f f'] =
      H[fun ω : U × P × U' × B => ω.2.2.2 | fun ω => (ω.1, ω.2.2.1) ;
        hkLaw Z pU pP pU' pP' f f'] -
      H[fun ω : U × P × U' × B => ω.2.2.2 | fun ω => (f ω.1 ω.2.1, ω.2.2.1) ;
        hkLaw Z pU pP pU' pP' f f'] := by
  rw [sel_info]
  congr 1
  exact condEntropy_cond_of_injective _ (e := fun v : U × U' => (some v.1, (none : Option P),
    some v.2)) (fun a b h => by simpa [Prod.ext_iff] using h) fun ω => by simp [selectThree]

private lemma sel_info₁₂ :
    I[fun ω : U × P × U' × B => selectThree {1, 2} (ω.1, ω.2.1, ω.2.2.1) : fun ω => ω.2.2.2 |
        fun ω => selectThree {1, 2}ᶜ (ω.1, ω.2.1, ω.2.2.1) ; hkLaw Z pU pP pU' pP' f f'] =
      H[fun ω : U × P × U' × B => ω.2.2.2 | fun ω => ω.1 ; hkLaw Z pU pP pU' pP' f f'] -
      H[fun ω : U × P × U' × B => ω.2.2.2 | fun ω => (f ω.1 ω.2.1, ω.2.2.1) ;
        hkLaw Z pU pP pU' pP' f f'] := by
  rw [sel_info]
  congr 1
  exact condEntropy_cond_of_injective _ (e := fun v : U => (some v, (none : Option P),
    (none : Option U'))) (fun a b h => by simpa using h) fun ω => by simp [selectThree]

end Mine2

section Master

variable {A₁ A₂ B₁ B₂ V₁ V₂ P₁ P₂ : Type u} [Fintype A₁] [Fintype A₂] [Fintype B₁] [Fintype B₂]
  [Fintype V₁] [Fintype V₂] [Fintype P₁] [Fintype P₂]
  [MeasurableSpace A₁] [MeasurableSpace A₂] [MeasurableSpace B₁] [MeasurableSpace B₂]
  [MeasurableSpace V₁] [MeasurableSpace V₂] [MeasurableSpace P₁] [MeasurableSpace P₂]
  [MeasurableSingletonClass A₁] [MeasurableSingletonClass A₂] [MeasurableSingletonClass B₁]
  [MeasurableSingletonClass B₂] [MeasurableSingletonClass V₁] [MeasurableSingletonClass V₂]
  [MeasurableSingletonClass P₁] [MeasurableSingletonClass P₂]
  (W : DMC (A₁ × A₂) (B₁ × B₂)) (pU₁ : PMF V₁) (pP₁ : PMF P₁) (pU₂ : PMF V₂) (pP₂ : PMF P₂)
  (f₁ : V₁ → P₁ → A₁) (f₂ : V₂ → P₂ → A₂)

omit [Fintype A₁] [Fintype A₂] [Fintype B₁] [Fintype B₂] [Fintype P₁] [Fintype P₂] [Fintype V₁]
  [Fintype V₂] [MeasurableSingletonClass P₂] [MeasurableSpace P₂] in
private lemma master₁ [Finite A₁] [Finite V₁] [Finite B₂] [Finite A₂] [Finite B₁] [Finite P₁]
    [Finite V₂] :
    (hkJointMeasure W (PMF.pure ()) (fun _ => pU₁.bind fun v => pP₁.map fun p => (v, f₁ v p))
        (fun _ => pU₂.bind fun v => pP₂.map fun p => (v, f₂ v p))).map
      (fun ω => (ω.2.1.1, ω.2.1.2, ω.2.2.1.1, ω.2.2.2.1)) =
    (hkLaw (out₁ W) pU₁ pP₁ pU₂ pP₂ f₁ f₂).map
      (fun ω => (ω.1, f₁ ω.1 ω.2.1, ω.2.2.1, ω.2.2.2)) := by
  have := Fintype.ofFinite A₁
  have := Fintype.ofFinite V₁
  have := Fintype.ofFinite B₂
  have := Fintype.ofFinite A₂
  have := Fintype.ofFinite B₁
  have := Fintype.ofFinite P₁
  have := Fintype.ofFinite V₂
  rw [hkJointMeasure, hkLaw, PMF.toMeasure_map _ _ (measurable_of_finite _),
    PMF.toMeasure_map _ _ (measurable_of_finite _)]
  congr 1
  simp only [DMC.jointPMF, PMF.pure_bind, PMF.map_bind, PMF.bind_bind, PMF.bind_map, PMF.map_comp,
    out₁, Function.comp_def]

omit [Fintype A₁] [Fintype A₂] [Fintype B₁] [Fintype B₂] [Fintype P₁] [Fintype P₂] [Fintype V₁]
  [Fintype V₂] [MeasurableSingletonClass P₁] [MeasurableSpace P₁] in
private lemma master₂ [Finite P₂] [Finite A₁] [Finite V₁] [Finite B₂] [Finite A₂] [Finite B₁]
    [Finite V₂] :
    (hkJointMeasure W (PMF.pure ()) (fun _ => pU₁.bind fun v => pP₁.map fun p => (v, f₁ v p))
        (fun _ => pU₂.bind fun v => pP₂.map fun p => (v, f₂ v p))).map
      (fun ω => (ω.2.2.1.1, ω.2.2.1.2, ω.2.1.1, ω.2.2.2.2)) =
    (hkLaw (fun a => out₂ W a.swap) pU₂ pP₂ pU₁ pP₁ f₂ f₁).map
      (fun ω => (ω.1, f₂ ω.1 ω.2.1, ω.2.2.1, ω.2.2.2)) := by
  have := Fintype.ofFinite P₂
  have := Fintype.ofFinite A₁
  have := Fintype.ofFinite V₁
  have := Fintype.ofFinite B₂
  have := Fintype.ofFinite A₂
  have := Fintype.ofFinite B₁
  have := Fintype.ofFinite V₂
  rw [hkJointMeasure, hkLaw, PMF.toMeasure_map _ _ (measurable_of_finite _),
    PMF.toMeasure_map _ _ (measurable_of_finite _)]
  congr 1
  simp only [DMC.jointPMF, PMF.pure_bind, PMF.map_bind, PMF.bind_bind, PMF.bind_map, PMF.map_comp,
    out₂, Function.comp_def]
  simp_rw [PMF.bind_comm pP₁ pU₂]
  rw [PMF.bind_comm pU₁ pU₂]
  simp_rw [PMF.bind_comm pP₁ pP₂, PMF.bind_comm pU₁ pP₂]
  rfl

end Master

section Transfer

variable {A₁ A₂ B₁ B₂ V₁ V₂ P₁ P₂ : Type u} [Fintype A₁] [Fintype A₂] [Fintype B₁] [Fintype B₂]
  [Fintype V₁] [Fintype V₂] [Fintype P₁] [Fintype P₂]
  [MeasurableSpace A₁] [MeasurableSpace A₂] [MeasurableSpace B₁] [MeasurableSpace B₂]
  [MeasurableSpace V₁] [MeasurableSpace V₂] [MeasurableSpace P₁] [MeasurableSpace P₂]
  [MeasurableSingletonClass A₁] [MeasurableSingletonClass A₂] [MeasurableSingletonClass B₁]
  [MeasurableSingletonClass B₂] [MeasurableSingletonClass V₁] [MeasurableSingletonClass V₂]
  [MeasurableSingletonClass P₁] [MeasurableSingletonClass P₂]
  (W : DMC (A₁ × A₂) (B₁ × B₂)) (pU₁ : PMF V₁) (pP₁ : PMF P₁) (pU₂ : PMF V₂) (pP₂ : PMF P₂)
  (f₁ : V₁ → P₁ → A₁) (f₂ : V₂ → P₂ → A₂)

private noncomputable def jm : Measure (Unit × (V₁ × A₁) × (V₂ × A₂) × (B₁ × B₂)) :=
  hkJointMeasure W (PMF.pure ()) (fun _ => pU₁.bind fun v => pP₁.map fun p => (v, f₁ v p))
    (fun _ => pU₂.bind fun v => pP₂.map fun p => (v, f₂ v p))

omit [Fintype A₁] [Fintype A₂] [Fintype B₂] [Fintype P₁] [Fintype P₂] [Fintype V₁] [Fintype V₂] in
omit [MeasurableSingletonClass P₂] [MeasurableSpace P₂] in
private lemma transfer₁ [Finite P₂] [Finite A₁] [Finite V₁] [Finite B₂] [Finite A₂] [Finite P₁]
    [Finite V₂] {T : Type*} [Fintype T] [MeasurableSpace T]
    (G : V₁ × A₁ × V₂ → T) :
    H[fun ω : Unit × (V₁ × A₁) × (V₂ × A₂) × (B₁ × B₂) => ω.2.2.2.1 |
        fun ω => G (ω.2.1.1, ω.2.1.2, ω.2.2.1.1) ; jm W pU₁ pP₁ pU₂ pP₂ f₁ f₂] =
      H[fun ω : V₁ × P₁ × V₂ × B₁ => ω.2.2.2 | fun ω => G (ω.1, f₁ ω.1 ω.2.1, ω.2.2.1) ;
        hkLaw (out₁ W) pU₁ pP₁ pU₂ pP₂ f₁ f₂] := by
  have := Fintype.ofFinite P₂
  have := Fintype.ofFinite A₁
  have := Fintype.ofFinite V₁
  have := Fintype.ofFinite B₂
  have := Fintype.ofFinite A₂
  have := Fintype.ofFinite P₁
  have := Fintype.ofFinite V₂
  have h1 := condEntropy_map (jm W pU₁ pP₁ pU₂ pP₂ f₁ f₂)
    (g := fun ω => (ω.2.1.1, ω.2.1.2, ω.2.2.1.1, ω.2.2.2.1)) (measurable_of_finite _)
    (X := fun m : V₁ × A₁ × V₂ × B₁ => m.2.2.2) (Y := fun m => G (m.1, m.2.1, m.2.2.1))
    (measurable_of_finite _) (measurable_of_finite _)
  have h2 := condEntropy_map (hkLaw (out₁ W) pU₁ pP₁ pU₂ pP₂ f₁ f₂)
    (g := fun ω => (ω.1, f₁ ω.1 ω.2.1, ω.2.2.1, ω.2.2.2)) (measurable_of_finite _)
    (X := fun m : V₁ × A₁ × V₂ × B₁ => m.2.2.2) (Y := fun m => G (m.1, m.2.1, m.2.2.1))
    (measurable_of_finite _) (measurable_of_finite _)
  rw [jm, master₁] at h1
  exact h1.symm.trans h2

omit [Fintype A₁] [Fintype A₂] [Fintype B₁] [Fintype P₁] [Fintype P₂] [Fintype V₁] [Fintype V₂] in
omit [MeasurableSingletonClass P₁] [MeasurableSpace P₁] in
private lemma transfer₂ [Finite P₂] [Finite A₁] [Finite V₁] [Finite A₂] [Finite B₁] [Finite P₁]
    [Finite V₂] {T : Type*} [Fintype T] [MeasurableSpace T]
    (G : V₂ × A₂ × V₁ → T) :
    H[fun ω : Unit × (V₁ × A₁) × (V₂ × A₂) × (B₁ × B₂) => ω.2.2.2.2 |
        fun ω => G (ω.2.2.1.1, ω.2.2.1.2, ω.2.1.1) ; jm W pU₁ pP₁ pU₂ pP₂ f₁ f₂] =
      H[fun ω : V₂ × P₂ × V₁ × B₂ => ω.2.2.2 | fun ω => G (ω.1, f₂ ω.1 ω.2.1, ω.2.2.1) ;
        hkLaw (fun a => out₂ W a.swap) pU₂ pP₂ pU₁ pP₁ f₂ f₁] := by
  have := Fintype.ofFinite P₂
  have := Fintype.ofFinite A₁
  have := Fintype.ofFinite V₁
  have := Fintype.ofFinite A₂
  have := Fintype.ofFinite B₁
  have := Fintype.ofFinite P₁
  have := Fintype.ofFinite V₂
  have h1 := condEntropy_map (jm W pU₁ pP₁ pU₂ pP₂ f₁ f₂)
    (g := fun ω => (ω.2.2.1.1, ω.2.2.1.2, ω.2.1.1, ω.2.2.2.2)) (measurable_of_finite _)
    (X := fun m : V₂ × A₂ × V₁ × B₂ => m.2.2.2) (Y := fun m => G (m.1, m.2.1, m.2.2.1))
    (measurable_of_finite _) (measurable_of_finite _)
  have h2 := condEntropy_map (hkLaw (fun a => out₂ W a.swap) pU₂ pP₂ pU₁ pP₁ f₂ f₁)
    (g := fun ω => (ω.1, f₂ ω.1 ω.2.1, ω.2.2.1, ω.2.2.2)) (measurable_of_finite _)
    (X := fun m : V₂ × A₂ × V₁ × B₂ => m.2.2.2) (Y := fun m => G (m.1, m.2.1, m.2.2.1))
    (measurable_of_finite _) (measurable_of_finite _)
  rw [jm, master₂] at h1
  exact h1.symm.trans h2

end Transfer

section Quantities

variable {A₁ A₂ B₁ B₂ V₁ V₂ P₁ P₂ : Type u} [Fintype A₁] [Fintype A₂] [Fintype B₁] [Fintype B₂]
  [Fintype V₁] [Fintype V₂] [Fintype P₁] [Fintype P₂]
  [MeasurableSpace A₁] [MeasurableSpace A₂] [MeasurableSpace B₁] [MeasurableSpace B₂]
  [MeasurableSpace V₁] [MeasurableSpace V₂] [MeasurableSpace P₁] [MeasurableSpace P₂]
  [MeasurableSingletonClass A₁] [MeasurableSingletonClass A₂] [MeasurableSingletonClass B₁]
  [MeasurableSingletonClass B₂] [MeasurableSingletonClass V₁] [MeasurableSingletonClass V₂]
  [MeasurableSingletonClass P₁] [MeasurableSingletonClass P₂]
  (W : DMC (A₁ × A₂) (B₁ × B₂)) (pU₁ : PMF V₁) (pP₁ : PMF P₁) (pU₂ : PMF V₂) (pP₂ : PMF P₂)
  (f₁ : V₁ → P₁ → A₁) (f₂ : V₂ → P₂ → A₂)

local notation "Ω₀" => Unit × (V₁ × A₁) × (V₂ × A₂) × (B₁ × B₂)

local notation "𝓙" => jm W pU₁ pP₁ pU₂ pP₂ f₁ f₂

local notation "𝓛₁" => hkLaw (out₁ W) pU₁ pP₁ pU₂ pP₂ f₁ f₂

set_option quotPrecheck false in
local notation "𝓛₂" => hkLaw (fun a => out₂ W a.swap) pU₂ pP₂ pU₁ pP₁ f₂ f₁

omit [Fintype A₂] [Fintype B₂] [Fintype P₁] [Fintype P₂] [Fintype V₁] in
omit [MeasurableSingletonClass P₂] [MeasurableSpace P₂] in
private lemma hk_a [Finite P₂] [Finite V₁] [Finite B₂] [Finite A₂] [Finite P₁] :
    I[fun ω : Ω₀ => ω.2.1.2 : fun ω => ω.2.2.2.1 |
        fun ω => (ω.2.2.1.1, ω.1) ; 𝓙] =
      H[fun ω : V₁ × P₁ × V₂ × B₁ => ω.2.2.2 | fun ω => ω.2.2.1 ; 𝓛₁] -
      H[fun ω : V₁ × P₁ × V₂ × B₁ => ω.2.2.2 | fun ω => (f₁ ω.1 ω.2.1, ω.2.2.1) ; 𝓛₁] := by
  have := Fintype.ofFinite P₂
  have := Fintype.ofFinite V₁
  have := Fintype.ofFinite B₂
  have := Fintype.ofFinite A₂
  have := Fintype.ofFinite P₁
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy]
  congr 1
  · refine (condEntropy_cond_of_injective _ (Z := fun ω : Ω₀ =>
      ω.2.2.1.1) (e := fun v : V₂ => (v, ()))
      (fun a b h => by simp_all [Prod.ext_iff]) fun ω => rfl).trans ?_
    exact transfer₁ W pU₁ pP₁ pU₂ pP₂ f₁ f₂ (fun t : V₁ × A₁ × V₂ => t.2.2)
  · refine (condEntropy_cond_of_injective _ (Z := fun ω : Ω₀ => (ω.2.1.2, ω.2.2.1.1))
      (e := fun p : A₁ × V₂ => (p.1, (p.2, ())))
      (fun a b h => by simp_all [Prod.ext_iff]) fun ω => rfl).trans ?_
    exact transfer₁ W pU₁ pP₁ pU₂ pP₂ f₁ f₂ (fun t : V₁ × A₁ × V₂ => (t.2.1, t.2.2))

omit [Fintype A₂] [Fintype B₂] [Fintype P₁] [Fintype P₂] [Fintype V₁] in
omit [MeasurableSingletonClass P₂] [MeasurableSpace P₂] in
private lemma hk_c₁ [Finite P₂] [Finite V₁] [Finite B₂] [Finite A₂] [Finite P₁] :
    I[fun ω : Ω₀ => (ω.2.1.2, ω.2.2.1.1) : fun ω => ω.2.2.2.1 |
        fun ω => ω.1 ; 𝓙] =
      H[fun ω : V₁ × P₁ × V₂ × B₁ => ω.2.2.2 | fun _ => () ; 𝓛₁] -
      H[fun ω : V₁ × P₁ × V₂ × B₁ => ω.2.2.2 | fun ω => (f₁ ω.1 ω.2.1, ω.2.2.1) ; 𝓛₁] := by
  have := Fintype.ofFinite P₂
  have := Fintype.ofFinite V₁
  have := Fintype.ofFinite B₂
  have := Fintype.ofFinite A₂
  have := Fintype.ofFinite P₁
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy]
  congr 1
  · exact transfer₁ W pU₁ pP₁ pU₂ pP₂ f₁ f₂ (fun _ : V₁ × A₁ × V₂ => ())
  · refine (condEntropy_cond_of_injective _ (Z := fun ω : Ω₀ => (ω.2.1.2, ω.2.2.1.1))
      (e := fun p : A₁ × V₂ => (p, ()))
      (fun a b h => by simp_all [Prod.ext_iff]) fun ω => rfl).trans ?_
    exact transfer₁ W pU₁ pP₁ pU₂ pP₂ f₁ f₂ (fun t : V₁ × A₁ × V₂ => (t.2.1, t.2.2))

omit [Fintype A₂] [Fintype B₂] [Fintype P₁] [Fintype P₂] in
omit [MeasurableSingletonClass P₂] [MeasurableSpace P₂] in
private lemma hk_d₁ [Finite P₂] [Finite B₂] [Finite A₂] [Finite P₁] :
    I[fun ω : Ω₀ => ω.2.1.2 : fun ω => ω.2.2.2.1 |
        fun ω => (ω.2.1.1, ω.2.2.1.1, ω.1) ; 𝓙] =
      H[fun ω : V₁ × P₁ × V₂ × B₁ => ω.2.2.2 | fun ω => (ω.1, ω.2.2.1) ; 𝓛₁] -
      H[fun ω : V₁ × P₁ × V₂ × B₁ => ω.2.2.2 | fun ω => (f₁ ω.1 ω.2.1, ω.2.2.1) ; 𝓛₁] := by
  have := Fintype.ofFinite P₂
  have := Fintype.ofFinite B₂
  have := Fintype.ofFinite A₂
  have := Fintype.ofFinite P₁
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy]
  congr 1
  · refine (condEntropy_cond_of_injective _ (Z := fun ω : Ω₀ => (ω.2.1.1, ω.2.2.1.1))
      (e := fun p : V₁ × V₂ => (p.1, p.2, ()))
      (fun a b h => by simp_all [Prod.ext_iff]) fun ω => rfl).trans ?_
    exact transfer₁ W pU₁ pP₁ pU₂ pP₂ f₁ f₂ (fun t : V₁ × A₁ × V₂ => (t.1, t.2.2))
  · refine (condEntropy_cond_of_injective _ (Z := fun ω : Ω₀ => (ω.2.1.1, ω.2.1.2, ω.2.2.1.1))
      (e := fun t : V₁ × A₁ × V₂ => (t.2.1, (t.1, t.2.2, ())))
      (fun a b h => by simp_all [Prod.ext_iff]) fun ω => rfl).trans ?_
    rw [transfer₁ W pU₁ pP₁ pU₂ pP₂ f₁ f₂ (fun t : V₁ × A₁ × V₂ => t)]
    exact condEntropy_mid _ _ _ _ _ _ _

omit [Fintype A₂] [Fintype B₂] [Fintype P₁] [Fintype P₂] in
omit [MeasurableSingletonClass P₂] [MeasurableSpace P₂] in
private lemma hk_e₁ [Finite P₂] [Finite B₂] [Finite A₂] [Finite P₁] :
    I[fun ω : Ω₀ => (ω.2.1.2, ω.2.2.1.1) : fun ω => ω.2.2.2.1 |
        fun ω => (ω.2.1.1, ω.1) ; 𝓙] =
      H[fun ω : V₁ × P₁ × V₂ × B₁ => ω.2.2.2 | fun ω => ω.1 ; 𝓛₁] -
      H[fun ω : V₁ × P₁ × V₂ × B₁ => ω.2.2.2 | fun ω => (f₁ ω.1 ω.2.1, ω.2.2.1) ; 𝓛₁] := by
  have := Fintype.ofFinite P₂
  have := Fintype.ofFinite B₂
  have := Fintype.ofFinite A₂
  have := Fintype.ofFinite P₁
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy]
  congr 1
  · refine (condEntropy_cond_of_injective _ (Z := fun ω : Ω₀ => ω.2.1.1)
      (e := fun v : V₁ => (v, ()))
      (fun a b h => by simp_all [Prod.ext_iff]) fun ω => rfl).trans ?_
    exact transfer₁ W pU₁ pP₁ pU₂ pP₂ f₁ f₂ (fun t : V₁ × A₁ × V₂ => t.1)
  · refine (condEntropy_cond_of_injective _ (Z := fun ω : Ω₀ => (ω.2.1.1, ω.2.1.2, ω.2.2.1.1))
      (e := fun t : V₁ × A₁ × V₂ => ((t.2.1, t.2.2), (t.1, ())))
      (fun a b h => by simp_all [Prod.ext_iff]) fun ω => rfl).trans ?_
    rw [transfer₁ W pU₁ pP₁ pU₂ pP₂ f₁ f₂ (fun t : V₁ × A₁ × V₂ => t)]
    exact condEntropy_mid _ _ _ _ _ _ _

omit [Fintype A₁] [Fintype B₁] [Fintype P₁] [Fintype P₂] [Fintype V₂] in
omit [MeasurableSingletonClass P₁] [MeasurableSpace P₁] in
private lemma hk_b [Finite P₂] [Finite A₁] [Finite B₁] [Finite P₁] [Finite V₂] :
    I[fun ω : Ω₀ => ω.2.2.1.2 : fun ω => ω.2.2.2.2 |
        fun ω => (ω.2.1.1, ω.1) ; 𝓙] =
      H[fun ω : V₂ × P₂ × V₁ × B₂ => ω.2.2.2 | fun ω => ω.2.2.1 ; 𝓛₂] -
      H[fun ω : V₂ × P₂ × V₁ × B₂ => ω.2.2.2 | fun ω => (f₂ ω.1 ω.2.1, ω.2.2.1) ; 𝓛₂] := by
  have := Fintype.ofFinite P₂
  have := Fintype.ofFinite A₁
  have := Fintype.ofFinite B₁
  have := Fintype.ofFinite P₁
  have := Fintype.ofFinite V₂
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy]
  congr 1
  · refine (condEntropy_cond_of_injective _ (Z := fun ω : Ω₀ => ω.2.1.1)
      (e := fun v : V₁ => (v, ()))
      (fun a b h => by simp_all [Prod.ext_iff]) fun ω => rfl).trans ?_
    exact transfer₂ W pU₁ pP₁ pU₂ pP₂ f₁ f₂ (fun t : V₂ × A₂ × V₁ => t.2.2)
  · refine (condEntropy_cond_of_injective _ (Z := fun ω : Ω₀ => (ω.2.2.1.2, ω.2.1.1))
      (e := fun p : A₂ × V₁ => (p.1, (p.2, ())))
      (fun a b h => by simp_all [Prod.ext_iff]) fun ω => rfl).trans ?_
    exact transfer₂ W pU₁ pP₁ pU₂ pP₂ f₁ f₂ (fun t : V₂ × A₂ × V₁ => (t.2.1, t.2.2))

omit [Fintype A₁] [Fintype B₁] [Fintype P₁] [Fintype P₂] [Fintype V₂] in
omit [MeasurableSingletonClass P₁] [MeasurableSpace P₁] in
private lemma hk_c₂ [Finite P₂] [Finite A₁] [Finite B₁] [Finite P₁] [Finite V₂] :
    I[fun ω : Ω₀ => (ω.2.2.1.2, ω.2.1.1) : fun ω => ω.2.2.2.2 |
        fun ω => ω.1 ; 𝓙] =
      H[fun ω : V₂ × P₂ × V₁ × B₂ => ω.2.2.2 | fun _ => () ; 𝓛₂] -
      H[fun ω : V₂ × P₂ × V₁ × B₂ => ω.2.2.2 | fun ω => (f₂ ω.1 ω.2.1, ω.2.2.1) ; 𝓛₂] := by
  have := Fintype.ofFinite P₂
  have := Fintype.ofFinite A₁
  have := Fintype.ofFinite B₁
  have := Fintype.ofFinite P₁
  have := Fintype.ofFinite V₂
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy]
  congr 1
  · exact transfer₂ W pU₁ pP₁ pU₂ pP₂ f₁ f₂ (fun _ : V₂ × A₂ × V₁ => ())
  · refine (condEntropy_cond_of_injective _ (Z := fun ω : Ω₀ => (ω.2.2.1.2, ω.2.1.1))
      (e := fun p : A₂ × V₁ => (p, ()))
      (fun a b h => by simp_all [Prod.ext_iff]) fun ω => rfl).trans ?_
    exact transfer₂ W pU₁ pP₁ pU₂ pP₂ f₁ f₂ (fun t : V₂ × A₂ × V₁ => (t.2.1, t.2.2))

omit [Fintype A₁] [Fintype B₁] [Fintype P₁] [Fintype P₂] in
omit [MeasurableSingletonClass P₁] [MeasurableSpace P₁] in
private lemma hk_d₂ [Finite P₂] [Finite A₁] [Finite B₁] [Finite P₁] :
    I[fun ω : Ω₀ => ω.2.2.1.2 : fun ω => ω.2.2.2.2 |
        fun ω => (ω.2.1.1, ω.2.2.1.1, ω.1) ; 𝓙] =
      H[fun ω : V₂ × P₂ × V₁ × B₂ => ω.2.2.2 | fun ω => (ω.1, ω.2.2.1) ; 𝓛₂] -
      H[fun ω : V₂ × P₂ × V₁ × B₂ => ω.2.2.2 | fun ω => (f₂ ω.1 ω.2.1, ω.2.2.1) ; 𝓛₂] := by
  have := Fintype.ofFinite P₂
  have := Fintype.ofFinite A₁
  have := Fintype.ofFinite B₁
  have := Fintype.ofFinite P₁
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy]
  congr 1
  · refine (condEntropy_cond_of_injective _ (Z := fun ω : Ω₀ => (ω.2.2.1.1, ω.2.1.1))
      (e := fun p : V₂ × V₁ => (p.2, p.1, ()))
      (fun a b h => by simp_all [Prod.ext_iff]) fun ω => rfl).trans ?_
    exact transfer₂ W pU₁ pP₁ pU₂ pP₂ f₁ f₂ (fun t : V₂ × A₂ × V₁ => (t.1, t.2.2))
  · refine (condEntropy_cond_of_injective _ (Z := fun ω : Ω₀ => (ω.2.2.1.1, ω.2.2.1.2, ω.2.1.1))
      (e := fun t : V₂ × A₂ × V₁ => (t.2.1, (t.2.2, t.1, ())))
      (fun a b h => by simp_all [Prod.ext_iff]) fun ω => rfl).trans ?_
    rw [transfer₂ W pU₁ pP₁ pU₂ pP₂ f₁ f₂ (fun t : V₂ × A₂ × V₁ => t)]
    exact condEntropy_mid _ _ _ _ _ _ _

omit [Fintype A₁] [Fintype B₁] [Fintype P₁] [Fintype P₂] in
omit [MeasurableSingletonClass P₁] [MeasurableSpace P₁] in
private lemma hk_e₂ [Finite P₂] [Finite A₁] [Finite B₁] [Finite P₁] :
    I[fun ω : Ω₀ => (ω.2.2.1.2, ω.2.1.1) : fun ω => ω.2.2.2.2 |
        fun ω => (ω.2.2.1.1, ω.1) ; 𝓙] =
      H[fun ω : V₂ × P₂ × V₁ × B₂ => ω.2.2.2 | fun ω => ω.1 ; 𝓛₂] -
      H[fun ω : V₂ × P₂ × V₁ × B₂ => ω.2.2.2 | fun ω => (f₂ ω.1 ω.2.1, ω.2.2.1) ; 𝓛₂] := by
  have := Fintype.ofFinite P₂
  have := Fintype.ofFinite A₁
  have := Fintype.ofFinite B₁
  have := Fintype.ofFinite P₁
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy]
  congr 1
  · refine (condEntropy_cond_of_injective _ (Z := fun ω : Ω₀ =>
      ω.2.2.1.1) (e := fun v : V₂ => (v, ()))
      (fun a b h => by simp_all [Prod.ext_iff]) fun ω => rfl).trans ?_
    exact transfer₂ W pU₁ pP₁ pU₂ pP₂ f₁ f₂ (fun t : V₂ × A₂ × V₁ => t.1)
  · refine (condEntropy_cond_of_injective _ (Z := fun ω : Ω₀ => (ω.2.2.1.1, ω.2.2.1.2, ω.2.1.1))
      (e := fun t : V₂ × A₂ × V₁ => ((t.2.1, t.2.2), (t.1, ())))
      (fun a b h => by simp_all [Prod.ext_iff]) fun ω => rfl).trans ?_
    rw [transfer₂ W pU₁ pP₁ pU₂ pP₂ f₁ f₂ (fun t : V₂ × A₂ × V₁ => t)]
    exact condEntropy_mid _ _ _ _ _ _ _

end Quantities

section Inclusion

variable {A₁ A₂ B₁ B₂ V₁ V₂ P₁ P₂ : Type u} [Fintype A₁] [Fintype A₂] [Fintype B₁] [Fintype B₂]
  [Fintype V₁] [Fintype V₂] [Fintype P₁] [Fintype P₂]
  [MeasurableSpace A₁] [MeasurableSpace A₂] [MeasurableSpace B₁] [MeasurableSpace B₂]
  [MeasurableSpace V₁] [MeasurableSpace V₂] [MeasurableSpace P₁] [MeasurableSpace P₂]
  [MeasurableSingletonClass A₁] [MeasurableSingletonClass A₂] [MeasurableSingletonClass B₁]
  [MeasurableSingletonClass B₂] [MeasurableSingletonClass V₁] [MeasurableSingletonClass V₂]
  [MeasurableSingletonClass P₁] [MeasurableSingletonClass P₂]

theorem hanKobayashi1981Region_subset_hkRegion (W : DMC (A₁ × A₂) (B₁ × B₂)) (pU₁ : PMF V₁)
    (pP₁ : PMF P₁) (pU₂ : PMF V₂) (pP₂ : PMF P₂) (f₁ : V₁ → P₁ → A₁) (f₂ : V₂ → P₂ → A₂) :
    hanKobayashi1981Region W pU₁ pP₁ pU₂ pP₂ f₁ f₂ ⊆
      hkRegion W (PMF.pure ()) (fun _ => pU₁.bind fun v => pP₁.map fun p => (v, f₁ v p))
        (fun _ => pU₂.bind fun v => pP₂.map fun p => (v, f₂ v p)) := by
  rintro ⟨R₁, R₂⟩ ⟨r₁₀, r₁₁, r₂₀, r₂₁, h₁₀, h₁₁, h₂₀, h₂₁, h1, h2, hS⟩
  simp only at h1 h2
  subst h1 h2
  obtain ⟨s01, t01⟩ := hS {0, 1}
  obtain ⟨sU, tU⟩ := hS univ
  obtain ⟨s1, t1⟩ := hS {1}
  obtain ⟨s12, t12⟩ := hS {1, 2}
  rw [sel_info₀₁] at s01 t01
  rw [sel_info_univ] at sU tU
  rw [sel_info₁] at s1 t1
  rw [sel_info₁₂] at s12 t12
  simp only [Fin.sum_univ_three, sum_singleton, sum_insert, mem_singleton,
    Fin.reduceEq, not_false_eq_true, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at s01 t01 sU tU s1 t1 s12 t12
  have ha := hk_a W pU₁ pP₁ pU₂ pP₂ f₁ f₂
  have hb := hk_b W pU₁ pP₁ pU₂ pP₂ f₁ f₂
  have hc₁ := hk_c₁ W pU₁ pP₁ pU₂ pP₂ f₁ f₂
  have hc₂ := hk_c₂ W pU₁ pP₁ pU₂ pP₂ f₁ f₂
  have hd₁ := hk_d₁ W pU₁ pP₁ pU₂ pP₂ f₁ f₂
  have hd₂ := hk_d₂ W pU₁ pP₁ pU₂ pP₂ f₁ f₂
  have he₁ := hk_e₁ W pU₁ pP₁ pU₂ pP₂ f₁ f₂
  have he₂ := hk_e₂ W pU₁ pP₁ pU₂ pP₂ f₁ f₂
  simp only [jm] at ha hb hc₁ hc₂ hd₁ hd₂ he₁ he₂
  simp only [hkRegion, Set.mem_ofPred_eq]
  refine ⟨by positivity, by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end Inclusion

end IC

end Meat
