# Disproof of TLMC Conjecture 00000001050

**Verdict: FALSE**

## 原文逐字引用与对象对应关系(对象一致纪律)

 conjectures/00000001050.md 英文定义句逐字引用:

> **English.** Conjecture: For any composition of a permutation polynomial f with a linearized polynomial, the image under the relative trace F_{q²}/F_q is everything if and only if the kernel is trivial (a relative-trace surjectivity criterion).

中文句逐字引用:

> **中文。** 猜想:任何置换多项式 f 与线性化的复合在 F_{q^2}/F_q 相对迹上的像为全像的判据为核平凡(相对迹满射判据)。

对应关系声明(本文攻击的每个对象与原文定义一一对应):

| 原文对象 | 本攻击中的实例 |
|---|---|
| 域 F_{q²}/F_q | q = 2,F₄ = F₂(ω),ω² = ω + 1;相对迹 Tr_{F₄/F₂}(z) = z + z² |
| permutation polynomial f | f = id ∈ F₄[x](F₄ 的恒等置换,是置换多项式) |
| linearized polynomial | L(x) = ωx + ωx² = ω(x + x²) ∈ F₄[x](指数为 2⁰, 2¹,系数取自 F₄,是 F₂-线性化的) |
| composition(复合) | g = L ∘ f = L ∘ id = L(由于 f = id,两种复合次序 L∘id 与 id∘L 相同) |
| "the image under the relative trace is everything" | Tr_{F₄/F₂}(g(F₄)) = Tr_{F₄/F₂}(L(F₄)) = F₂(= {0, 1},即素域全体) |
| "the kernel" | ker g = ker L = {x ∈ F₄ : L(x) = 0}(f = id 时复合的核与线性化多项式的核相同) |
| "if and only if" | 双条件 "像为全像 ⟺ 核平凡" |

## 攻击(反例)

在 F₄ = F₂(ω)(ω² = ω + 1,ω³ = 1)上逐点计算:

| x | x + x² | L(x) = ω(x + x²) | Tr_{F₄/F₂}(L(x)) = L(x) + L(x)² |
|---|---|---|---|
| 0 | 0 | 0 | 0 |
| 1 | 1 + 1 = 0 | 0 | 0 |
| ω | ω + ω² = 1 | ω | ω + ω² = 1 |
| ω² | ω² + ω⁴ = ω² + ω = 1 | ω | ω + ω² = 1 |

- **核非平凡**:ker L = {x : x + x² = 0} = {0, 1} = F₂ ⊊ F₄,即 ker L ≠ {0}。
- **相对迹像为全像**:L(F₄) = {0, ω},故 Tr_{F₄/F₂}(L(F₄)) = {Tr(0), Tr(ω)} = {0, ω + ω²} = {0, 1} = F₂,满射成立。

于是双条件中"⟹ 像 为全像 ⟹ 核平凡"一侧被否:满射成立而核非平凡,故 "像为全像 ⟺ 核平凡" 为假。猜想被证伪。

注:x + x² = 0 ⟺ x² = x ⟺ x ∈ F₂(x² − x 在任一域上至多两个根,且 0、1 显然为其根),这是 ker L = {0,1} 的独立验证;Tr_{F₄/F₂}(z) = z + z² 是 q = 2 时相对迹的标准定义(z + z^q)。

## Lean 验证

`lean4/Main.lean` 将 F₄ 编码为 4 构造子的归纳类型并显式给出加法/乘法/Frobenius 平方表,定义 `lin`(= L∘id)、`trace`(相对迹)、`trCompose`(Tr∘L),并证明:

- `F4.surjective_true`:Tr∘L 的像包含 0 与 1(满射 onto 素域);
- `F4.kernel_not_trivial`:1 ∈ ker L 且 1 ≠ 0;
- `F4.criterion_false`:¬(Surjective ↔ KernelTrivial)。

全部断言由 `rfl` 与构造子穷尽(`cases`)闭合,**零公理、零 sorry**;`lean4/Check.lean` 对每个定理 `#print axioms`。

## 边界(不主张的内容)

- 本反例只否定原文陈述的双条件本身(q = 2、f = id 的最小情形);不主张"核平凡 ⟹ 满射"方向在一般情形成立或不成立,该方向未被触及。
- 由于取 f = id,两种复合次序重合;本攻击不对 f ≠ id 的情形下其他方向下界作任何断言。
- 不排除原文在附加假设(如对 L 的次数/核维数限制)下有可修正版本;本提交仅针对逐字引用的原始陈述。
- 复现:`python3 reproduce.py`(独立重算,无第三方依赖);Lean 侧 `cd lean4 && lake build && lake env lean Check.lean`。
