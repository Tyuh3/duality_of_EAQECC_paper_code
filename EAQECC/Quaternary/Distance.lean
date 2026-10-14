import EAQECC.Quaternary.SubspaceTransport

/-!
四元加性码中子空间差集上的最小汉明重量，及其与二元最小辛重量的对应。
-/

namespace Quantum
namespace Quaternary

/-- 子空间差集上的最小汉明重量。要求 C 中不属于 W 的向量重量至少为 d，
存在达到 d 的向量，且 d 为正数。空差集不满足此条件。
以下证明非空差集上最小重量存在且唯一。
-/
def HasMinimumHammingWeightOutside {n : ℕ}
    (V W : QuaternaryAdditiveCode n) (d : ℕ) : Prop :=
  1 ≤ d ∧
    (∀ u : QuaternaryVector n,
      u ∈ V → u ∉ W → d ≤ hammingWeight u) ∧
    (∃ u : QuaternaryVector n,
      u ∈ V ∧ u ∉ W ∧ hammingWeight u = d)

theorem exists_hasMinimumHammingWeightOutside
    {n : ℕ} (V W : QuaternaryAdditiveCode n)
    (hNonempty : ∃ u : QuaternaryVector n, u ∈ V ∧ u ∉ W) :
    ∃ d : ℕ, HasMinimumHammingWeightOutside V W d := by
  classical
  let Attained : ℕ → Prop := fun d ↦
    ∃ u : QuaternaryVector n,
      u ∈ V ∧ u ∉ W ∧ hammingWeight u = d
  have hAttained : ∃ d : ℕ, Attained d := by
    obtain ⟨u, huV, huW⟩ := hNonempty
    exact ⟨hammingWeight u, u, huV, huW, rfl⟩
  let d := Nat.find hAttained
  obtain ⟨u, huV, huW, hWeight⟩ := Nat.find_spec hAttained
  have hdPos : 1 ≤ d := by
    change 1 ≤ Nat.find hAttained
    rw [← hWeight]
    apply Nat.one_le_iff_ne_zero.mpr
    intro hZero
    have huZero := (hammingWeight_eq_zero_iff u).mp hZero
    subst u
    exact huW W.zero_mem
  have hLower : ∀ v : QuaternaryVector n,
      v ∈ V → v ∉ W → d ≤ hammingWeight v := by
    intro v hvV hvW
    exact Nat.find_min' hAttained ⟨v, hvV, hvW, rfl⟩
  exact ⟨d, hdPos, hLower, ⟨u, huV, huW, hWeight⟩⟩

theorem HasMinimumHammingWeightOutside.unique
    {n d d' : ℕ} {V W : QuaternaryAdditiveCode n}
    (h : HasMinimumHammingWeightOutside V W d)
    (h' : HasMinimumHammingWeightOutside V W d') :
    d = d' := by
  obtain ⟨u, huV, huW, hWeight⟩ := h.2.2
  obtain ⟨u', huV', huW', hWeight'⟩ := h'.2.2
  apply Nat.le_antisymm
  · simpa [hWeight'] using h.2.1 u' huV' huW'
  · simpa [hWeight] using h'.2.1 u huV huW

/- 二元与四元映射保持子空间差集。以下分别处理迹对偶或原码中排除根空间后的向量集合。
-/
theorem binaryToQuaternary_image_subspaceDifference
    {n : ℕ} (V W : BinarySymplecticSubspace n) :
    Set.image (binaryToQuaternary n)
        ((V : Set (BinarySymplecticVector n)) \ W) =
      ((binaryToQuaternarySubspace V : QuaternaryAdditiveCode n) :
          Set (QuaternaryVector n)) \
        binaryToQuaternarySubspace W := by
  ext u
  constructor
  · rintro ⟨v, ⟨hvV, hvW⟩, rfl⟩
    exact ⟨by simpa using hvV, by simpa using hvW⟩
  · rintro ⟨huV, huW⟩
    refine ⟨quaternaryToBinary n u, ?_, by simp⟩
    exact ⟨by simpa using huV, by simpa using huW⟩

theorem quaternaryToBinary_image_subspaceDifference
    {n : ℕ} (C D : QuaternaryAdditiveCode n) :
    Set.image (quaternaryToBinary n)
        ((C : Set (QuaternaryVector n)) \ D) =
      ((quaternaryToBinarySubspace C : BinarySymplecticSubspace n) :
          Set (BinarySymplecticVector n)) \
        quaternaryToBinarySubspace D := by
  ext v
  constructor
  · rintro ⟨u, ⟨huC, huD⟩, rfl⟩
    exact ⟨by simpa using huC, by simpa using huD⟩
  · rintro ⟨hvC, hvD⟩
    refine ⟨binaryToQuaternary n v, ?_, by simp⟩
    exact ⟨by simpa using hvC, by simpa using hvD⟩

theorem quaternaryToBinary_image_traceOrthogonal_diff_traceRadical
    {n : ℕ} (C : QuaternaryAdditiveCode n) :
    Set.image (quaternaryToBinary n)
        (((traceOrthogonal C : QuaternaryAdditiveCode n) :
            Set (QuaternaryVector n)) \
          traceRadical C) =
      (((NQubitPauliGroupElement.sympOrthogonal
            (quaternaryToBinarySubspace C) : BinarySymplecticSubspace n) :
          Set (BinarySymplecticVector n)) \
        symplecticRadical (quaternaryToBinarySubspace C)) := by
  rw [quaternaryToBinary_image_subspaceDifference,
    quaternaryToBinarySubspace_traceOrthogonal,
    quaternaryToBinarySubspace_traceRadical]

theorem quaternaryToBinary_image_code_diff_traceRadical
    {n : ℕ} (C : QuaternaryAdditiveCode n) :
    Set.image (quaternaryToBinary n)
        ((C : Set (QuaternaryVector n)) \ traceRadical C) =
      ((quaternaryToBinarySubspace C : BinarySymplecticSubspace n) :
          Set (BinarySymplecticVector n)) \
        symplecticRadical (quaternaryToBinarySubspace C) := by
  rw [quaternaryToBinary_image_subspaceDifference,
    quaternaryToBinarySubspace_traceRadical]

/- 结合差集与重量保持关系，将最小汉明重量条件等价地转化为最小辛重量条件。
-/
theorem hasMinimumHammingWeightOutside_binaryToQuaternarySubspace_iff
    {n d : ℕ} (V W : BinarySymplecticSubspace n) :
    HasMinimumHammingWeightOutside
        (binaryToQuaternarySubspace V)
        (binaryToQuaternarySubspace W) d ↔
      HasMinimumSymplecticWeightOutside V W d := by
  constructor
  · rintro ⟨hd, hLower, u, huV, huW, hWeight⟩
    refine ⟨hd, ?_, ?_⟩
    · intro v hvV hvW
      have h := hLower (binaryToQuaternary n v) (by simpa) (by simpa)
      simpa using h
    · refine ⟨quaternaryToBinary n u, ?_, ?_, ?_⟩
      · simpa using huV
      · simpa using huW
      · simpa using hWeight
  · rintro ⟨hd, hLower, v, hvV, hvW, hWeight⟩
    refine ⟨hd, ?_, ?_⟩
    · intro u huV huW
      have h := hLower (quaternaryToBinary n u)
        (by simpa using huV) (by simpa using huW)
      simpa using h
    · refine ⟨binaryToQuaternary n v, ?_, ?_, ?_⟩
      · simpa
      · simpa
      · simpa using hWeight

theorem hasMinimumHammingWeightOutside_iff_preimage
    {n d : ℕ} (C D : QuaternaryAdditiveCode n) :
    HasMinimumHammingWeightOutside C D d ↔
      HasMinimumSymplecticWeightOutside
        (quaternaryToBinarySubspace C)
        (quaternaryToBinarySubspace D) d := by
  simpa using
    (hasMinimumHammingWeightOutside_binaryToQuaternarySubspace_iff
      (d := d) (quaternaryToBinarySubspace C)
      (quaternaryToBinarySubspace D))

theorem hasMinimumHammingWeight_traceOrthogonal_diff_traceRadical_iff
    {n d : ℕ} (C : QuaternaryAdditiveCode n) :
    HasMinimumHammingWeightOutside
        (traceOrthogonal C) (traceRadical C) d ↔
      HasMinimumSymplecticWeightOutside
        (NQubitPauliGroupElement.sympOrthogonal
          (quaternaryToBinarySubspace C))
        (symplecticRadical (quaternaryToBinarySubspace C)) d := by
  rw [hasMinimumHammingWeightOutside_iff_preimage,
    quaternaryToBinarySubspace_traceOrthogonal,
    quaternaryToBinarySubspace_traceRadical]

theorem hasMinimumHammingWeight_code_diff_traceRadical_iff
    {n d : ℕ} (C : QuaternaryAdditiveCode n) :
    HasMinimumHammingWeightOutside C (traceRadical C) d ↔
      HasMinimumSymplecticWeightOutside
        (quaternaryToBinarySubspace C)
        (symplecticRadical (quaternaryToBinarySubspace C)) d := by
  rw [hasMinimumHammingWeightOutside_iff_preimage,
    quaternaryToBinarySubspace_traceRadical]

end Quaternary
end Quantum
