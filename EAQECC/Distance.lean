import EAQECC.Basic
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance

/-!
纠缠辅助稳定子码的发送端最小距离。错误仅作用于发送端，辅助端附加恒等算子。
-/

namespace Quantum

/- 在发送端算子后附加 c 个恒等算子。以下证明发送端作用及重量保持不变。
-/
def NQubitPauliOperator.appendIdentity
    {n : ℕ}
    (op : NQubitPauliOperator n)
    (c : ℕ) :
    NQubitPauliOperator (n + c) :=
  Fin.addCases op (fun _ => PauliOperator.I)

@[simp]
theorem NQubitPauliOperator.appendIdentity_apply_castAdd
    {n : ℕ}
    (op : NQubitPauliOperator n)
    (c : ℕ)
    (i : Fin n) :
    op.appendIdentity c (Fin.castAdd c i) = op i := by
  simp [appendIdentity]

@[simp]
theorem NQubitPauliOperator.appendIdentity_apply_natAdd
    {n : ℕ}
    (op : NQubitPauliOperator n)
    (c : ℕ)
    (j : Fin c) :
    op.appendIdentity c (Fin.natAdd n j) = PauliOperator.I := by
  simp [appendIdentity]

@[simp]
theorem NQubitPauliOperator.appendIdentity_identity
    (n c : ℕ) :
    (NQubitPauliOperator.identity n).appendIdentity c =
      NQubitPauliOperator.identity (n + c) := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [NQubitPauliOperator.identity]

theorem NQubitPauliOperator.support_appendIdentity
    {n : ℕ}
    (op : NQubitPauliOperator n)
    (c : ℕ) :
    NQubitPauliOperator.support (op.appendIdentity c) =
      (NQubitPauliOperator.support op).map (Fin.castAddEmb c) := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [NQubitPauliOperator.support]
  · simp [NQubitPauliOperator.support]
    intro x _ h
    have hval := congrArg Fin.val h
    simp at hval
    omega

@[simp]
theorem NQubitPauliOperator.weight_appendIdentity
    {n : ℕ}
    (op : NQubitPauliOperator n)
    (c : ℕ) :
    NQubitPauliOperator.weight (op.appendIdentity c) =
      NQubitPauliOperator.weight op := by
  rw [NQubitPauliOperator.weight, NQubitPauliOperator.support_appendIdentity,
    Finset.card_map, NQubitPauliOperator.weight]

namespace StabilizerGroup.StabilizerCode

/-- 发送端最小距离。要求 d 为正数，所有非平凡逻辑错误的发送端重量至少为 d，
并存在重量恰为 d 的错误。判定逻辑作用时，先在辅助端附加恒等算子，
再使用扩展稳定子码的非平凡逻辑算子条件；重量仍只计发送端。
-/
def HasBaseDistance
    {n c k : ℕ}
    (Q : StabilizerGroup.StabilizerCode (n + c) k)
    (d : ℕ) : Prop :=
  1 ≤ d ∧
    (∀ op : NQubitPauliOperator n,
      StabilizerGroup.IsNontrivialLogicalOperator
          (NQubitPauliGroupElement.ofOperator (op.appendIdentity c))
          Q.toStabilizerGroup →
        d ≤ NQubitPauliOperator.weight op) ∧
    (∃ op : NQubitPauliOperator n,
      StabilizerGroup.IsNontrivialLogicalOperator
          (NQubitPauliGroupElement.ofOperator (op.appendIdentity c))
          Q.toStabilizerGroup ∧
        NQubitPauliOperator.weight op = d)

end StabilizerGroup.StabilizerCode

namespace EACode

/-- 纠缠辅助码的非平凡逻辑算子。发送端错误在辅助端补恒等作用后，
保持码空间，并在忽略整体相位后对编码态产生非平凡逻辑作用。
仅与稳定子元素相差整体相位的算子被排除。
-/
def IsNontrivialLogicalOperator
    {n k c : ℕ}
    (Q : EACode n k c)
    (op : NQubitPauliOperator n) : Prop :=
  StabilizerGroup.IsNontrivialLogicalOperator
    (NQubitPauliGroupElement.ofOperator (op.appendIdentity c))
    Q.extendedCode.toStabilizerGroup

theorem weight_pos_of_isNontrivialLogicalOperator
    {n k c : ℕ}
    (Q : EACode n k c)
    (op : NQubitPauliOperator n)
    (hLogical : Q.IsNontrivialLogicalOperator op) :
    0 < NQubitPauliOperator.weight op := by
  apply Nat.pos_of_ne_zero
  intro hWeight
  have hop : op = NQubitPauliOperator.identity n :=
    (NQubitPauliOperator.weight_eq_zero_iff op).mp hWeight
  unfold IsNontrivialLogicalOperator at hLogical
  have hNotMem :=
    ((StabilizerGroup.IsNontrivialLogicalOperator_iff
      (NQubitPauliGroupElement.ofOperator (op.appendIdentity c))
      Q.extendedCode.toStabilizerGroup).mp hLogical).2.1
  apply hNotMem
  simpa [hop, NQubitPauliGroupElement.ofOperator,
    NQubitPauliGroupElement.one_def] using
      Q.extendedCode.toStabilizerGroup.one_mem

/- 将扩展稳定子码的发送端距离作为纠缠辅助码的距离。
以下引理提取重量下界与达到下界的算子，并给出距离的判定方法及唯一性。
-/
def HasDistance
    {n k c : ℕ}
    (Q : EACode n k c)
    (d : ℕ) : Prop :=
  StabilizerGroup.StabilizerCode.HasBaseDistance
    (n := n) (c := c) Q.extendedCode d

theorem HasDistance.one_le_d
    {n k c : ℕ}
    (Q : EACode n k c)
    (d : ℕ)
    (h : Q.HasDistance d) :
    1 ≤ d :=
  h.1

theorem HasDistance.min_weight
    {n k c : ℕ}
    (Q : EACode n k c)
    (d : ℕ)
    (h : Q.HasDistance d)
    (op : NQubitPauliOperator n)
    (hLogical : Q.IsNontrivialLogicalOperator op) :
    d ≤ NQubitPauliOperator.weight op :=
  h.2.1 op hLogical

theorem HasDistance.exists_weight_eq
    {n k c : ℕ}
    (Q : EACode n k c)
    (d : ℕ)
    (h : Q.HasDistance d) :
    ∃ op : NQubitPauliOperator n,
      Q.IsNontrivialLogicalOperator op ∧
      NQubitPauliOperator.weight op = d :=
  h.2.2

theorem hasDistance_of
    {n k c : ℕ}
    (Q : EACode n k c)
    (d : ℕ)
    (hd : 1 ≤ d)
    (hWitness : ∃ op : NQubitPauliOperator n,
      Q.IsNontrivialLogicalOperator op ∧
      NQubitPauliOperator.weight op = d)
    (hMin : ∀ w : ℕ, 1 ≤ w → w < d →
      ∀ op : NQubitPauliOperator n,
        NQubitPauliOperator.weight op = w →
        ¬Q.IsNontrivialLogicalOperator op) :
    Q.HasDistance d := by
  refine ⟨hd, ?_, hWitness⟩
  intro op hLogical
  by_cases hWeight : NQubitPauliOperator.weight op < d
  · have hPos : 0 < NQubitPauliOperator.weight op :=
      Q.weight_pos_of_isNontrivialLogicalOperator op hLogical
    have hOne : 1 ≤ NQubitPauliOperator.weight op := Nat.one_le_iff_ne_zero.mpr hPos.ne'
    exact absurd hLogical
      (hMin (NQubitPauliOperator.weight op) hOne hWeight op rfl)
  · omega

theorem HasDistance.unique
    {n k c d d' : ℕ}
    (Q : EACode n k c)
    (h : Q.HasDistance d)
    (h' : Q.HasDistance d') :
    d = d' := by
  obtain ⟨op, hLogical, hWeight⟩ := h.exists_weight_eq Q d
  obtain ⟨op', hLogical', hWeight'⟩ := h'.exists_weight_eq Q d'
  apply Nat.le_antisymm
  · simpa [hWeight'] using h.min_weight Q d op' hLogical'
  · simpa [hWeight] using h'.min_weight Q d' op hLogical

end EACode

/-- 带距离的纠缠辅助稳定子码。在已有码结构上附加发送端最小距离为 d 的证明。
-/
structure EACodeWithDistance (n k d c : ℕ)
    extends EACode n k c where
  hasDistance : toEACode.HasDistance d

namespace EACodeWithDistance

theorem one_le_d
    {n k d c : ℕ}
    (Q : EACodeWithDistance n k d c) :
    1 ≤ d :=
  Q.hasDistance.one_le_d Q.toEACode d

theorem min_weight
    {n k d c : ℕ}
    (Q : EACodeWithDistance n k d c)
    (op : NQubitPauliOperator n)
    (hLogical : Q.toEACode.IsNontrivialLogicalOperator op) :
    d ≤ NQubitPauliOperator.weight op :=
  Q.hasDistance.min_weight Q.toEACode d op hLogical

theorem exists_weight_eq
    {n k d c : ℕ}
    (Q : EACodeWithDistance n k d c) :
    ∃ op : NQubitPauliOperator n,
      Q.toEACode.IsNontrivialLogicalOperator op ∧
      NQubitPauliOperator.weight op = d :=
  Q.hasDistance.exists_weight_eq Q.toEACode d

end EACodeWithDistance

end Quantum
