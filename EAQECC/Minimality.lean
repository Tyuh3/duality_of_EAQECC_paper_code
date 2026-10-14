import EAQECC.Basic

/-!
固定候选生成元的辅助量子比特数下界。利用扩展后的对易性，
把发送端冲突矩阵写成辅助端检查矩阵与辛形式矩阵的乘积。
-/

namespace Quantum

/- 对应原生成元与扩展生成元的索引，并利用限制关系恢复发送端作用。
-/
def CanExtendWith.extendedIndex
    {n c' : ℕ}
    {C : GeneratorListCandidate n}
    (h : CanExtendWith C c')
    (i : Fin C.generatorsList.length) :
    Fin h.extendedCode.generatorsList.length :=
  Fin.cast (by
    have hlen := congrArg List.length h.restrict_eq
    simpa using hlen.symm) i

theorem CanExtendWith.restrict_get
    {n c' : ℕ}
    {C : GeneratorListCandidate n}
    (h : CanExtendWith C c')
    (i : Fin C.generatorsList.length) :
    restrictToBaseGroupElement n c'
      (h.extendedCode.generatorsList.get (h.extendedIndex i)) =
    C.generatorsList.get i := by
  let L := h.extendedCode.generatorsList
  let f : NQubitPauliGroupElement (n + c') → NQubitPauliGroupElement n :=
    fun g => restrictToBaseGroupElement n c' g
  have hlen : L.length = C.generatorsList.length := by
    have hlen_map := congrArg List.length h.restrict_eq
    simpa [L, f] using hlen_map
  change f (L.get (Fin.cast hlen.symm i)) = C.generatorsList.get i
  have hget :=
    List.get_of_eq h.restrict_eq
      (Fin.cast (by simp [L]) (Fin.cast hlen.symm i))
  simpa [L, f, List.get_eq_getElem, List.getElem_map] using hget

theorem CanExtendWith.conflictMatrix_eq_aux
    {n c' : ℕ}
    {C : GeneratorListCandidate n}
    (h : CanExtendWith C c')
    (i j : Fin C.generatorsList.length) :
    GeneratorListCandidate.conflictMatrix C i j =
      NQubitPauliOperator.symplecticInner
        ((restrictToAuxGroupElement n c'
          (h.extendedCode.generatorsList.get (h.extendedIndex i))).operators)
        ((restrictToAuxGroupElement n c'
          (h.extendedCode.generatorsList.get (h.extendedIndex j))).operators) := by
  let gi := h.extendedCode.generatorsList.get (h.extendedIndex i)
  let gj := h.extendedCode.generatorsList.get (h.extendedIndex j)
  have hgi_mem :
      gi ∈ NQubitPauliGroupElement.listToSet h.extendedCode.generatorsList := by
    change gi ∈ h.extendedCode.generatorsList
    exact List.get_mem _ _
  have hgj_mem :
      gj ∈ NQubitPauliGroupElement.listToSet h.extendedCode.generatorsList := by
    change gj ∈ h.extendedCode.generatorsList
    exact List.get_mem _ _
  have hcomm : gi * gj = gj * gi :=
    h.extendedCode.generators_commute gi hgi_mem gj hgj_mem
  have hfull_zero :
      NQubitPauliOperator.symplecticInner gi.operators gj.operators = 0 :=
    (NQubitPauliOperator.commutes_iff_symplectic_inner_zero gi gj).1 hcomm
  have hsplit := symplecticInner_restrict_base_aux n c' gi gj
  have hsum :
      NQubitPauliOperator.symplecticInner
        (restrictToBaseGroupElement n c' gi).operators
        (restrictToBaseGroupElement n c' gj).operators +
      NQubitPauliOperator.symplecticInner
        (restrictToAuxGroupElement n c' gi).operators
        (restrictToAuxGroupElement n c' gj).operators = 0 := by
    rwa [hsplit] at hfull_zero
  have hbase_eq_aux :
      NQubitPauliOperator.symplecticInner
        (restrictToBaseGroupElement n c' gi).operators
        (restrictToBaseGroupElement n c' gj).operators =
      NQubitPauliOperator.symplecticInner
        (restrictToAuxGroupElement n c' gi).operators
        (restrictToAuxGroupElement n c' gj).operators := by
    calc
      NQubitPauliOperator.symplecticInner
          (restrictToBaseGroupElement n c' gi).operators
          (restrictToBaseGroupElement n c' gj).operators
          =
        NQubitPauliOperator.symplecticInner
          (restrictToBaseGroupElement n c' gi).operators
          (restrictToBaseGroupElement n c' gj).operators + 0 := by simp
      _ =
        NQubitPauliOperator.symplecticInner
          (restrictToBaseGroupElement n c' gi).operators
          (restrictToBaseGroupElement n c' gj).operators +
        (NQubitPauliOperator.symplecticInner
          (restrictToAuxGroupElement n c' gi).operators
          (restrictToAuxGroupElement n c' gj).operators +
        NQubitPauliOperator.symplecticInner
          (restrictToAuxGroupElement n c' gi).operators
          (restrictToAuxGroupElement n c' gj).operators) := by
          rw [show
            NQubitPauliOperator.symplecticInner
              (restrictToAuxGroupElement n c' gi).operators
              (restrictToAuxGroupElement n c' gj).operators +
            NQubitPauliOperator.symplecticInner
              (restrictToAuxGroupElement n c' gi).operators
              (restrictToAuxGroupElement n c' gj).operators = 0 by
              ring_nf
              rw [show (2 : ZMod 2) = 0 from CharP.cast_eq_zero (ZMod 2) 2, mul_zero]]
      _ =
        (NQubitPauliOperator.symplecticInner
          (restrictToBaseGroupElement n c' gi).operators
          (restrictToBaseGroupElement n c' gj).operators +
        NQubitPauliOperator.symplecticInner
          (restrictToAuxGroupElement n c' gi).operators
          (restrictToAuxGroupElement n c' gj).operators) +
        NQubitPauliOperator.symplecticInner
          (restrictToAuxGroupElement n c' gi).operators
          (restrictToAuxGroupElement n c' gj).operators := by abel
      _ =
        0 +
        NQubitPauliOperator.symplecticInner
          (restrictToAuxGroupElement n c' gi).operators
          (restrictToAuxGroupElement n c' gj).operators := by rw [hsum]
      _ =
        NQubitPauliOperator.symplecticInner
          (restrictToAuxGroupElement n c' gi).operators
          (restrictToAuxGroupElement n c' gj).operators := by simp
  calc
    GeneratorListCandidate.conflictMatrix C i j =
        NQubitPauliOperator.symplecticInner
          (C.generatorsList.get i).operators
          (C.generatorsList.get j).operators := rfl
    _ =
        NQubitPauliOperator.symplecticInner
          (restrictToBaseGroupElement n c' gi).operators
          (restrictToBaseGroupElement n c' gj).operators := by
          rw [h.restrict_get i, h.restrict_get j]
    _ =
        NQubitPauliOperator.symplecticInner
          (restrictToAuxGroupElement n c' gi).operators
          (restrictToAuxGroupElement n c' gj).operators := hbase_eq_aux

/- 辅助端冲突矩阵。扩展生成元对易，因此辅助端与发送端的冲突矩阵相同。
-/
def CanExtendWith.auxConflictMatrix
    {n c' : ℕ}
    {C : GeneratorListCandidate n}
    (h : CanExtendWith C c') :
    Matrix
      (Fin C.generatorsList.length)
      (Fin C.generatorsList.length)
      (ZMod 2) :=
  fun i j =>
    NQubitPauliOperator.symplecticInner
      ((restrictToAuxGroupElement n c'
        (h.extendedCode.generatorsList.get (h.extendedIndex i))).operators)
      ((restrictToAuxGroupElement n c'
        (h.extendedCode.generatorsList.get (h.extendedIndex j))).operators)

theorem CanExtendWith.conflictMatrix_eq_auxConflictMatrix
    {n c' : ℕ}
    {C : GeneratorListCandidate n}
    (h : CanExtendWith C c') :
    GeneratorListCandidate.conflictMatrix C = h.auxConflictMatrix := by
  ext i j
  exact h.conflictMatrix_eq_aux i j

/- 辅助坐标上的辛形式矩阵与检查矩阵。以下矩阵分解给出冲突秩不超过 2c′。
-/
def auxSymplecticMatrix (c : ℕ) :
    Matrix (Fin c ⊕ Fin c) (Fin c ⊕ Fin c) (ZMod 2) :=
  fun a b =>
    match a, b with
    | Sum.inl i, Sum.inr j => if i = j then 1 else 0
    | Sum.inr i, Sum.inl j => if i = j then 1 else 0
    | _, _ => 0

def CanExtendWith.auxCheckMatrix
    {n c' : ℕ}
    {C : GeneratorListCandidate n}
    (h : CanExtendWith C c') :
    Matrix (Fin C.generatorsList.length) (Fin c' ⊕ Fin c') (ZMod 2) :=
  fun i a =>
    let op := (restrictToAuxGroupElement n c'
      (h.extendedCode.generatorsList.get (h.extendedIndex i))).operators
    match a with
    | Sum.inl q => (op q).toSymplecticSingle.1
    | Sum.inr q => (op q).toSymplecticSingle.2

theorem CanExtendWith.auxConflictMatrix_eq_auxCheckMatrix_mul
    {n c' : ℕ}
    {C : GeneratorListCandidate n}
    (h : CanExtendWith C c') :
    h.auxConflictMatrix =
      h.auxCheckMatrix * auxSymplecticMatrix c' * h.auxCheckMatrix.transpose := by
  ext i j
  simp [CanExtendWith.auxConflictMatrix, CanExtendWith.auxCheckMatrix,
    auxSymplecticMatrix, Matrix.mul_apply, NQubitPauliOperator.symplecticInner,
    PauliOperator.symplecticProductSingle]
  rw [Finset.sum_add_distrib]
  abel

theorem CanExtendWith.auxConflictMatrix_rank_le_two_mul
    {n c' : ℕ}
    {C : GeneratorListCandidate n}
    (h : CanExtendWith C c') :
    Matrix.rank h.auxConflictMatrix ≤ 2 * c' := by
  rw [h.auxConflictMatrix_eq_auxCheckMatrix_mul]
  calc
    Matrix.rank (h.auxCheckMatrix * auxSymplecticMatrix c' * h.auxCheckMatrix.transpose) ≤
        Matrix.rank (h.auxCheckMatrix * auxSymplecticMatrix c') :=
      Matrix.rank_mul_le_left _ _
    _ ≤ Matrix.rank h.auxCheckMatrix :=
      Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin c' ⊕ Fin c') :=
      Matrix.rank_le_card_width _
    _ = 2 * c' := by
      simp [Nat.two_mul]

/- 由冲突秩上界推出任意给定扩展的辅助量子比特数下界。
-/
theorem GeneratorListCandidate.conflictRank_le_two_mul_of_canExtendWith
    {n c' : ℕ}
    (C : GeneratorListCandidate n)
    (h : CanExtendWith C c') :
    GeneratorListCandidate.conflictRank C ≤ 2 * c' := by
  unfold GeneratorListCandidate.conflictRank
  rw [h.conflictMatrix_eq_auxConflictMatrix]
  exact h.auxConflictMatrix_rank_le_two_mul

theorem GeneratorListCandidate.ebitCount_le_of_canExtendWith
    {n c' : ℕ}
    (C : GeneratorListCandidate n)
    (h : CanExtendWith C c') :
    GeneratorListCandidate.ebitCount C ≤ c' := by
  unfold GeneratorListCandidate.ebitCount
  exact Nat.div_le_of_le_mul
    (GeneratorListCandidate.conflictRank_le_two_mul_of_canExtendWith C h)

/-- 固定候选生成元下的纠缠参数下界。若另一扩展也恢复同一生成元列表，
其辅助量子比特数 c′ 必须满足 c ≤ c′。这里比较的是同一候选生成元的扩展。
-/
theorem EACode.c_minimal
    {n k c c' : ℕ}
    (Q : EACode n k c)
    (h : CanExtendWith Q.generators c') :
    c ≤ c' := by
  rw [Q.ebits_minimal]
  exact GeneratorListCandidate.ebitCount_le_of_canExtendWith Q.generators h

end Quantum
