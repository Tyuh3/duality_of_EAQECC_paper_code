import QEC.Stabilizer.Framework.Symplectic.IndependentEquiv
import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Data.Finset.Prod

/-!
纠缠辅助稳定子码的基本模型。用候选生成元的冲突矩阵记录非对易关系，
并要求辅助扩展得到的普通稳定子码在发送端恢复原生成元。
-/

namespace Quantum

/-- 候选稳定子生成元。保存整体相位为零的 Pauli 生成元及其二元辛向量线性无关性。
此处不要求生成元两两对易，非对易关系由下面的冲突矩阵记录。
-/
structure GeneratorListCandidate (n : ℕ) where

  generatorsList : List (NQubitPauliGroupElement n)

  generators_phaseZero :
    NQubitPauliGroupElement.AllPhaseZero generatorsList

  generators_rowsIndependent :
    NQubitPauliGroupElement.rowsLinearIndependent generatorsList

/-- 冲突矩阵。第 i、j 项为两生成元的辛内积：零表示对易，一表示反对易。
它记录辅助扩展需要补偿的非对易关系。
-/
def GeneratorListCandidate.conflictMatrix {n : ℕ} (C : GeneratorListCandidate n) :
    Matrix
      (Fin C.generatorsList.length)
      (Fin C.generatorsList.length)
      (ZMod 2) :=
  fun i j =>
    NQubitPauliOperator.symplecticInner
      ((C.generatorsList.get i).operators)
      ((C.generatorsList.get j).operators)

/- 以下证明冲突矩阵对称且对角线为零，并将其视为交替双线性形式。
-/
def GeneratorListCandidate.IsSelfOrthogonal {n : ℕ} (C : GeneratorListCandidate n) : Prop :=
  ∀ i j : Fin C.generatorsList.length,
    GeneratorListCandidate.conflictMatrix C i j = 0

@[simp]
theorem GeneratorListCandidate.conflictMatrix_apply
    {n : ℕ}
    (C : GeneratorListCandidate n)
    (i j : Fin C.generatorsList.length) :
    GeneratorListCandidate.conflictMatrix C i j =
      NQubitPauliOperator.symplecticInner
        ((C.generatorsList.get i).operators)
        ((C.generatorsList.get j).operators) := by
  rfl

theorem GeneratorListCandidate.conflictMatrix_diag_zero
    {n : ℕ}
    (C : GeneratorListCandidate n)
    (i : Fin C.generatorsList.length) :
    GeneratorListCandidate.conflictMatrix C i i = 0 := by
  unfold GeneratorListCandidate.conflictMatrix NQubitPauliOperator.symplecticInner
  apply Finset.sum_eq_zero
  intro q _
  cases (C.generatorsList.get i).operators q <;>
    simp [PauliOperator.symplecticProductSingle]
  decide

theorem GeneratorListCandidate.conflictMatrix_symmetric
    {n : ℕ}
    (C : GeneratorListCandidate n)
    (i j : Fin C.generatorsList.length) :
    GeneratorListCandidate.conflictMatrix C i j =
      GeneratorListCandidate.conflictMatrix C j i := by
  unfold GeneratorListCandidate.conflictMatrix NQubitPauliOperator.symplecticInner
  apply Finset.sum_congr rfl
  intro q _
  cases (C.generatorsList.get i).operators q <;>
    cases (C.generatorsList.get j).operators q <;>
      simp [PauliOperator.symplecticProductSingle]

theorem GeneratorListCandidate.conflictMatrix_zero_diagonal
    {n : ℕ}
    (C : GeneratorListCandidate n) :
    ∀ i : Fin C.generatorsList.length,
      GeneratorListCandidate.conflictMatrix C i i = 0 :=
  GeneratorListCandidate.conflictMatrix_diag_zero C

theorem GeneratorListCandidate.conflictMatrix_isSymm
    {n : ℕ}
    (C : GeneratorListCandidate n) :
    Matrix.IsSymm (GeneratorListCandidate.conflictMatrix C) := by
  apply Matrix.IsSymm.ext
  intro i j
  exact GeneratorListCandidate.conflictMatrix_symmetric C j i

theorem GeneratorListCandidate.conflictMatrix_alternating
    {n : ℕ}
    (C : GeneratorListCandidate n) :
    Matrix.IsSymm (GeneratorListCandidate.conflictMatrix C) ∧
      (∀ i : Fin C.generatorsList.length,
        GeneratorListCandidate.conflictMatrix C i i = 0) :=
  ⟨GeneratorListCandidate.conflictMatrix_isSymm C,
    GeneratorListCandidate.conflictMatrix_zero_diagonal C⟩

noncomputable def GeneratorListCandidate.conflictBilinForm
    {n : ℕ}
    (C : GeneratorListCandidate n) :
    LinearMap.BilinForm (ZMod 2)
      (Fin C.generatorsList.length → ZMod 2) :=
  Matrix.toBilin' (GeneratorListCandidate.conflictMatrix C)

@[simp]
theorem GeneratorListCandidate.conflictBilinForm_toMatrix
    {n : ℕ}
    (C : GeneratorListCandidate n) :
    LinearMap.BilinForm.toMatrix'
        (GeneratorListCandidate.conflictBilinForm C) =
      GeneratorListCandidate.conflictMatrix C := by
  unfold GeneratorListCandidate.conflictBilinForm
  simp

@[simp]
theorem GeneratorListCandidate.conflictBilinForm_single_single
    {n : ℕ}
    (C : GeneratorListCandidate n)
    (i j : Fin C.generatorsList.length) :
    GeneratorListCandidate.conflictBilinForm C (Pi.single i 1) (Pi.single j 1) =
      GeneratorListCandidate.conflictMatrix C i j := by
  unfold GeneratorListCandidate.conflictBilinForm
  simp

theorem GeneratorListCandidate.conflictBilinForm_single_self_zero
    {n : ℕ}
    (C : GeneratorListCandidate n)
    (i : Fin C.generatorsList.length) :
    GeneratorListCandidate.conflictBilinForm C (Pi.single i 1) (Pi.single i 1) = 0 := by
  rw [GeneratorListCandidate.conflictBilinForm_single_single]
  exact GeneratorListCandidate.conflictMatrix_diag_zero C i

theorem GeneratorListCandidate.matrix_toBilin_self_zero_of_diag_zero_symmetric
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (ZMod 2))
    (hdiag : ∀ i, M i i = 0)
    (hsymm : ∀ i j, M i j = M j i)
    (x : ι → ZMod 2) :
    Matrix.toBilin' M x x = 0 := by
  rw [Matrix.toBilin'_apply]
  rw [← Finset.sum_product']
  rw [← Finset.diag_union_offDiag (s := Finset.univ)]
  rw [Finset.sum_union (Finset.disjoint_diag_offDiag _)]
  have hdiagSum :
      (∑ p ∈ (Finset.univ : Finset ι).diag,
        x p.1 * M p.1 p.2 * x p.2) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_diag] at hp
    rcases hp with ⟨-, hp_eq⟩
    rw [hp_eq, hdiag]
    simp
  have hoffDiagSum :
      (∑ p ∈ (Finset.univ : Finset ι).offDiag,
        x p.1 * M p.1 p.2 * x p.2) = 0 := by
    refine Finset.sum_involution (s := (Finset.univ : Finset ι).offDiag)
      (f := fun p : ι × ι => x p.1 * M p.1 p.2 * x p.2)
      (g := fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only
      rw [hsymm p.2 p.1]
      ring_nf
      rw [show (2 : ZMod 2) = 0 from CharP.cast_eq_zero (ZMod 2) 2, mul_zero]
    · intro p hp hp_ne hp_swap
      apply hp_ne
      cases p with
      | mk i j =>
        simp at hp_swap ⊢
        obtain ⟨-, hij⟩ := hp_swap
        rw [hij, hdiag]
        simp
    · intro p hp
      rw [Finset.mem_offDiag]
      rw [Finset.mem_offDiag] at hp
      exact ⟨Finset.mem_univ _, Finset.mem_univ _, hp.2.2.symm⟩
    · intro p hp
      cases p
      rfl
  rw [hdiagSum, hoffDiagSum, add_zero]

theorem GeneratorListCandidate.conflictBilinForm_self_zero
    {n : ℕ}
    (C : GeneratorListCandidate n)
    (x : Fin C.generatorsList.length → ZMod 2) :
    GeneratorListCandidate.conflictBilinForm C x x = 0 := by
  unfold GeneratorListCandidate.conflictBilinForm
  exact GeneratorListCandidate.matrix_toBilin_self_zero_of_diag_zero_symmetric
    (GeneratorListCandidate.conflictMatrix C)
    (GeneratorListCandidate.conflictMatrix_diag_zero C)
    (GeneratorListCandidate.conflictMatrix_symmetric C)
    x

theorem GeneratorListCandidate.conflictBilinForm_isAlt
    {n : ℕ}
    (C : GeneratorListCandidate n) :
    (GeneratorListCandidate.conflictBilinForm C).IsAlt :=
  GeneratorListCandidate.conflictBilinForm_self_zero C

/- 冲突秩及其一半给出的纠缠参数。后续引理说明冲突秩为偶数时两者的关系。
-/
noncomputable def GeneratorListCandidate.conflictRank {n : ℕ} (C : GeneratorListCandidate n) : ℕ :=
  Matrix.rank (GeneratorListCandidate.conflictMatrix C)

noncomputable def GeneratorListCandidate.ebitCount {n : ℕ} (C : GeneratorListCandidate n) : ℕ :=
  GeneratorListCandidate.conflictRank C / 2

theorem GeneratorListCandidate.two_mul_ebitCount_eq_conflictRank_of_even
    {n : ℕ}
    (C : GeneratorListCandidate n)
    (hrank_even : Even (GeneratorListCandidate.conflictRank C)) :
    2 * GeneratorListCandidate.ebitCount C =
      GeneratorListCandidate.conflictRank C := by
  rcases hrank_even with ⟨r, hr⟩
  unfold GeneratorListCandidate.ebitCount
  rw [hr]
  omega

/- 发送端与辅助端的限制映射。后续引理将扩展算子的辛内积分解为两部分。
-/
def restrictToBaseGroupElement
    (n c : ℕ)
    (g : NQubitPauliGroupElement (n + c)) :
    NQubitPauliGroupElement n where
  phasePower := g.phasePower
  operators := fun i =>
    g.operators (Fin.castLE (Nat.le_add_right n c) i)

def restrictToAuxGroupElement
    (n c : ℕ)
    (g : NQubitPauliGroupElement (n + c)) :
    NQubitPauliGroupElement c where
  phasePower := g.phasePower
  operators := fun i =>
    g.operators (Fin.natAdd n i)

theorem NQubitPauliOperator.symplecticInner_restrict_base_aux
    (n c : ℕ)
    (op₁ op₂ : NQubitPauliOperator (n + c)) :
    NQubitPauliOperator.symplecticInner op₁ op₂ =
      NQubitPauliOperator.symplecticInner
        (fun i : Fin n => op₁ (Fin.castLE (Nat.le_add_right n c) i))
        (fun i : Fin n => op₂ (Fin.castLE (Nat.le_add_right n c) i)) +
      NQubitPauliOperator.symplecticInner
        (fun i : Fin c => op₁ (Fin.natAdd n i))
        (fun i : Fin c => op₂ (Fin.natAdd n i)) := by
  unfold NQubitPauliOperator.symplecticInner
  rw [Fin.sum_univ_add]
  simp [Fin.castAdd, Fin.castLE]

theorem symplecticInner_restrict_base_aux
    (n c : ℕ)
    (g h : NQubitPauliGroupElement (n + c)) :
    NQubitPauliOperator.symplecticInner g.operators h.operators =
      NQubitPauliOperator.symplecticInner
        (restrictToBaseGroupElement n c g).operators
        (restrictToBaseGroupElement n c h).operators +
      NQubitPauliOperator.symplecticInner
        (restrictToAuxGroupElement n c g).operators
        (restrictToAuxGroupElement n c h).operators := by
  simpa [restrictToBaseGroupElement, restrictToAuxGroupElement]
    using NQubitPauliOperator.symplecticInner_restrict_base_aux n c g.operators h.operators

/-- 候选生成元的对易扩展。要求添加 c′ 个辅助量子比特后得到普通稳定子码，
且将扩展生成元限制到发送端，恰好恢复给定的候选生成元列表。
-/
structure CanExtendWith {n : ℕ} (C : GeneratorListCandidate n) (c' : ℕ) where
  k' : ℕ
  extendedCode : StabilizerGroup.StabilizerCode (n + c') k'
  restrict_eq :
    extendedCode.generatorsList.map
      (fun g => restrictToBaseGroupElement n c' g) =
    C.generatorsList

/-- 纠缠辅助稳定子码。保存 n 个发送端量子比特上的候选生成元，
以及添加 c 个辅助量子比特后得到的、编码 k 个逻辑量子比特的普通稳定子码。
字段同时记录生成元数、参数条件、冲突矩阵确定的纠缠数和发送端限制关系。
-/
structure EACode (n k c : ℕ) where
  generators : GeneratorListCandidate n
  k_add_c_le_n : k + c ≤ n
  generators_length : generators.generatorsList.length = n + c - k
  ebits_minimal : c = GeneratorListCandidate.ebitCount generators
  extendedCode : StabilizerGroup.StabilizerCode (n + c) k
  extended_generators_restrict_eq :
    extendedCode.generatorsList.map
      (fun g => restrictToBaseGroupElement n c g) =
    generators.generatorsList

namespace EACode

/- 以下由码结构中的字段导出参数界，并沿用候选生成元的冲突矩阵及其性质。
-/
theorem k_le_n {n k c : ℕ} (Q : EACode n k c) :
    k ≤ n :=
  (Nat.le_add_right k c).trans Q.k_add_c_le_n

theorem c_le_n {n k c : ℕ} (Q : EACode n k c) :
    c ≤ n := by
  have hc : c ≤ c + k := Nat.le_add_right c k
  have hc' : c ≤ k + c := by
    simp [Nat.add_comm] at hc ⊢
  exact hc'.trans Q.k_add_c_le_n

theorem k_le_n_add_c {n k c : ℕ} (Q : EACode n k c) :
    k ≤ n + c :=
  (Q.k_le_n).trans (Nat.le_add_right n c)

theorem generators_length_add_k_eq {n k c : ℕ} (Q : EACode n k c) :
    Q.generators.generatorsList.length + k = n + c := by
  rw [Q.generators_length]
  exact Nat.sub_add_cancel Q.k_le_n_add_c

def conflictMatrix {n k c : ℕ} (Q : EACode n k c) :
    Matrix
      (Fin Q.generators.generatorsList.length)
      (Fin Q.generators.generatorsList.length)
      (ZMod 2) :=
  GeneratorListCandidate.conflictMatrix Q.generators

noncomputable def conflictRank {n k c : ℕ} (Q : EACode n k c) : ℕ :=
  GeneratorListCandidate.conflictRank Q.generators

noncomputable def ebitCount {n k c : ℕ} (Q : EACode n k c) : ℕ :=
  GeneratorListCandidate.ebitCount Q.generators

theorem conflictMatrix_diag_zero {n k c : ℕ}
    (Q : EACode n k c)
    (i : Fin Q.generators.generatorsList.length) :
    Q.conflictMatrix i i = 0 := by
  unfold EACode.conflictMatrix
  exact GeneratorListCandidate.conflictMatrix_diag_zero Q.generators i

theorem conflictMatrix_symmetric {n k c : ℕ}
    (Q : EACode n k c)
    (i j : Fin Q.generators.generatorsList.length) :
    Q.conflictMatrix i j = Q.conflictMatrix j i := by
  unfold EACode.conflictMatrix
  exact GeneratorListCandidate.conflictMatrix_symmetric Q.generators i j

theorem conflictMatrix_isSymm {n k c : ℕ}
    (Q : EACode n k c) :
    Matrix.IsSymm Q.conflictMatrix := by
  apply Matrix.IsSymm.ext
  intro i j
  exact Q.conflictMatrix_symmetric j i

theorem conflictMatrix_alternating {n k c : ℕ}
    (Q : EACode n k c) :
    Matrix.IsSymm Q.conflictMatrix ∧
      (∀ i : Fin Q.generators.generatorsList.length, Q.conflictMatrix i i = 0) :=
  ⟨Q.conflictMatrix_isSymm, Q.conflictMatrix_diag_zero⟩

theorem conflictBilinForm_self_zero {n k c : ℕ}
    (Q : EACode n k c)
    (x : Fin Q.generators.generatorsList.length → ZMod 2) :
    GeneratorListCandidate.conflictBilinForm Q.generators x x = 0 :=
  GeneratorListCandidate.conflictBilinForm_self_zero Q.generators x

theorem conflictBilinForm_isAlt {n k c : ℕ}
    (Q : EACode n k c) :
    (GeneratorListCandidate.conflictBilinForm Q.generators).IsAlt :=
  GeneratorListCandidate.conflictBilinForm_isAlt Q.generators

theorem two_mul_c_eq_conflictRank_of_even {n k c : ℕ}
    (Q : EACode n k c)
    (hrank_even : Even Q.conflictRank) :
    2 * c = Q.conflictRank := by
  have hc :
      2 * c = 2 * GeneratorListCandidate.ebitCount Q.generators :=
    congrArg (fun t => 2 * t) Q.ebits_minimal
  have hrank_even' :
      Even (GeneratorListCandidate.conflictRank Q.generators) := by
    simpa [EACode.conflictRank] using hrank_even
  exact hc.trans
    (GeneratorListCandidate.two_mul_ebitCount_eq_conflictRank_of_even
      Q.generators hrank_even')

end EACode

end Quantum
