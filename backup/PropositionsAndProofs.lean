import VersoManual
import TPiLZh.Examples

open Verso.Genre Manual
open TPiLZh

set_option pp.rawOnError true
set_option linter.typography.dashes false

#doc (Manual) "命题与证明" =>
%%%
tag := "propositions-and-proofs"
htmlSplit := .never
file := "PropositionsAndProofs"
%%%
-- Propositions and Proofs

-- By now, you have seen some ways of defining objects and functions in
-- Lean. In this chapter, we will begin to explain how to write
-- mathematical assertions and proofs in the language of dependent type
-- theory as well.

前一章你已经看到了在 Lean 中定义对象和函数的一些方法。在本章中，我们还将开始解释如何用依值类型论的语言来编写数学命题和证明。

-- # Propositions as Types
# 命题即类型
%%%
tag := "propositions-as-types"
%%%

-- One strategy for proving assertions about objects defined in the
-- language of dependent type theory is to layer an assertion language
-- and a proof language on top of the definition language. But there is
-- no reason to multiply languages in this way: dependent type theory is
-- flexible and expressive, and there is no reason we cannot represent
-- assertions and proofs in the same general framework.

证明在依值类型论语言中定义的对象的断言（assertion）的一种策略是在定义语言之上分层断言语言和证明语言。但是，没有理由以这种方式重复使用多种语言：依值类型论是灵活和富有表现力的，我们也没有理由不能在同一个总框架中表示断言和证明。

-- For example, we could introduce a new type, {lean}`Prop`, to represent
-- propositions, and introduce constructors to build new propositions
-- from others.

例如，我们可引入一种新类型 {lean}`Prop`，来表示命题，然后引入用其他命题构造新命题的构造子。

```lean
def Implies (p q : Prop) : Prop := p → q
------
#check And     -- And (a b : Prop) : Prop

#check Or      -- Or (a b : Prop) : Prop

#check Not     -- Not (a : Prop) : Prop

#check Implies -- Implies (p q : Prop) : Prop

variable (p q r : Prop)

#check And p q                      -- p ∧ q : Prop

#check Or (And p q) r               -- p ∧ q ∨ r : Prop

#check Implies (And p q) (And q p)  -- Implies (p ∧ q) (q ∧ p) : Prop
```


```setup
variable (p : Prop)
structure Proof (p : Prop) : Type where
  proof : p
variable (t : p) (q r : Prop)
def Implies (p q : Prop) : Prop := p → q
universe u
variable (t1 t2 : p) {α : Type u} {β : Type v}
```

-- We could then introduce, for each element {lean}`p : Prop`, another type
-- {lean}`Proof p`, for the type of proofs of {lean}`p`.  An “axiom” would be a
-- constant of such a type.

对每个元素 {lean}`p : Prop`，可以引入另一个类型 {lean}`Proof p`，作为 {lean}`p` 的证明的类型。“公理”是这个类型中的常值。


```lean
def Implies (p q : Prop) : Prop := p → q
structure Proof (p : Prop) : Type where
  proof : p
------
#check Proof   -- Proof (p : Prop) : Type

axiom and_commut (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)

#check and_commut p q     -- and_commut p q : Proof (Implies (p ∧ q) (q ∧ p))
```



-- In addition to axioms, however, we would also need rules to build new
-- proofs from old ones. For example, in many proof systems for
-- propositional logic, we have the rule of _modus ponens_:

然而，除了公理之外，我们还需要从旧证明中建立新证明的规则。例如，在许多命题逻辑的证明系统中，我们有肯定前件式（modus ponens）推理规则:

-- > From a proof of {lean}`Implies p q` and a proof of {lean}`p`, we obtain a proof of {lean}`q`.

> 如果能证明 {lean}`Implies p q` 和 {lean}`p`，则能证明 {lean}`q`。

-- We could represent this as follows:

我们可以如下地表示它：

```lean
def Implies (p q : Prop) : Prop := p → q
structure Proof (p : Prop) : Type where
  proof : p
------
axiom modus_ponens (p q : Prop) :
  Proof (Implies p q) → Proof p →
  Proof q
```

-- Systems of natural deduction for propositional logic also typically rely on the following rule:

命题逻辑的自然演绎系统通常也依赖于以下规则：

-- > Suppose that, assuming {lean}`p` as a hypothesis, we have a proof of {lean}`q`. Then we can “cancel” the hypothesis and obtain a proof of {lean}`Implies p q`.

> 假设以 {lean}`p` 为前提，我们有 {lean}`q` 的证明。那么我们可以“取消”该假设并获得 {lean}`Implies p q` 的证明。

-- We could render this as follows:

我们可以将其呈现如下：

```lean
def Implies (p q : Prop) : Prop := p → q
structure Proof (p : Prop) : Type where
  proof : p
------
axiom implies_intro (p q : Prop) :
  (Proof p → Proof q) → Proof (Implies p q)
```

-- This approach would provide us with a reasonable way of building assertions and proofs.
-- Determining that an expression {lean}`t` is a correct proof of assertion {lean}`p` would then
-- simply be a matter of checking that {lean}`t` has type {lean}`Proof p`.

这种方法将为我们提供建立断言和证明的合理方式。确定表达式 {lean}`t` 是断言 {lean}`p` 的正确证明，只需检查 {lean}`t` 是否具有类型 {lean}`Proof p`。

-- Some simplifications are possible, however. To start with, we can
-- avoid writing the term {lean}`Proof` repeatedly by conflating {lean}`Proof p`
-- with {lean}`p` itself. In other words, whenever we have {lean}`p : Prop`, we
-- can interpret {lean}`p` as a type, namely, the type of its proofs. We can
-- then read {lean}`t : p` as the assertion that {lean}`t` is a proof of {lean}`p`.

然而，可以进行一些简化。首先，我们可以通过将 {lean}`Proof p` 与 {lean}`p` 本身合并来避免重复书写术语 {lean}`Proof`。换句话说，只要我们有 {lean}`p : Prop`，我们就可以将 {lean}`p` 解释为一个类型，即其证明的类型。然后我们可以将 {lean}`t : p` 读作 {lean}`t` 是 {lean}`p` 的证明的断言。

-- Moreover, once we make this identification, the rules for implication
-- show that we can pass back and forth between {lean}`Implies p q` and
-- {lean}`p → q`. In other words, implication between propositions {lean}`p` and {lean}`q`
-- corresponds to having a function that takes any element of {lean}`p` to an
-- element of {lean}`q`. As a result, the introduction of the connective
-- {lean}`Implies` is entirely redundant: we can use the usual function space
-- constructor {lean}`p → q` from dependent type theory as our notion of
-- implication.

此外，一旦我们进行了这种识别，蕴涵规则表明我们可以在 {lean}`Implies p q` 和 {lean}`p → q` 之间来回转换。换句话说，命题 {lean}`p` 和 {lean}`q` 之间的蕴涵对应于拥有一个将 {lean}`p` 的任何元素映射到 {lean}`q` 的元素的函数。结果，连接词 {lean}`Implies` 的引入完全是多余的：我们可以使用依值类型论中通常的函数空间构造子 {lean}`p → q` 作为我们的蕴涵概念。

-- This is the approach followed in the Calculus of Constructions, and
-- hence in Lean as well. The fact that the rules for implication in a
-- proof system for natural deduction correspond exactly to the rules
-- governing abstraction and application for functions is an instance of
-- the {deftech}_Curry-Howard isomorphism_, sometimes known as the
-- {deftech}_propositions-as-types_ paradigm. In fact, the type {lean}`Prop` is
-- syntactic sugar for {lean}`Sort 0`, the very bottom of the type hierarchy
-- described in the last chapter. Moreover, {lean}`Type u` is also just
-- syntactic sugar for {lean}`Sort (u+1)`. {lean}`Prop` has some special
-- features, but like the other type universes, it is closed under the
-- arrow constructor: if we have {lean}`p q : Prop`, then {lean}`p → q : Prop`.

这是构造演算（Calculus of Constructions）所采用的方法，因此也是 Lean 所采用的方法。自然演绎证明系统中的蕴涵规则与控制函数抽象和应用的规则完全对应，这一事实是 {deftech}_柯里-霍华德同构（Curry-Howard isomorphism）_ 的一个实例，有时称为 {deftech}_命题即类型（propositions-as-types）_ 范式。事实上，类型 {lean}`Prop` 是 {lean}`Sort 0` 的语法糖，即上一章描述的类型层次结构的最底层。此外，{lean}`Type u` 也只是 {lean}`Sort (u+1)` 的语法糖。{lean}`Prop` 有一些特殊功能，但像其他类型宇宙一样，它在箭头构造子下是封闭的：如果我们有 {lean}`p q : Prop`，那么 {lean}`p → q : Prop`。

-- There are at least two ways of thinking about propositions as
-- types. To some who take a constructive view of logic and mathematics,
-- this is a faithful rendering of what it means to be a proposition: a
-- proposition {lean}`p` represents a sort of data type, namely, a
-- specification of the type of data that constitutes a proof. A proof of
-- {lean}`p` is then simply an object {lean}`t : p` of the right type.

关于命题即类型，至少有两种思考方式。对于那些持逻辑和数学构造主义观点的人来说，这是对命题含义的忠实呈现：命题 {lean}`p` 代表一种数据类型，即构成证明的数据类型的规范。{lean}`p` 的证明仅仅是正确类型的对象 {lean}`t : p`。

-- Those not inclined to this ideology can view it, rather, as a simple
-- coding trick. To each proposition {lean}`p` we associate a type that is
-- empty if {lean}`p` is false and has a single element, say {lit}`*`, if {lean}`p`
-- is true. In the latter case, let us say that (the type associated
-- with) {lean}`p` is _inhabited_. It just so happens that the rules for
-- function application and abstraction can conveniently help us keep
-- track of which elements of {lean}`Prop` are inhabited. So constructing an
-- element {lean}`t : p` tells us that {lean}`p` is indeed true. You can think of
-- the inhabitant of {lean}`p` as being the “fact that {lean}`p` is true.” A
-- proof of {lean}`p → q` uses “the fact that {lean}`p` is true” to obtain “the
-- fact that {lean}`q` is true.”

那些不倾向于这种意识形态的人可以将其视为一种简单的编码技巧。对于每个命题 {lean}`p`，我们关联一个类型，如果 {lean}`p` 为假，则该类型为空；如果 {lean}`p` 为真，则该类型有一个元素，比如 {lit}`*`。在后一种情况下，我们说（与 {lean}`p` 关联的类型）是 _有居留的（inhabited）_。恰好函数应用和抽象的规则可以方便地帮助我们跟踪 {lean}`Prop` 的哪些元素是有居留的。因此，构造一个元素 {lean}`t : p` 告诉我们 {lean}`p` 确实为真。你可以将 {lean}`p` 的居留者视为“{lean}`p` 为真这一事实”。{lean}`p → q` 的证明使用“{lean}`p` 为真这一事实”来获得“{lean}`q` 为真这一事实”。

-- Indeed, if {lean}`p : Prop` is any proposition, Lean's kernel treats any
-- two elements {lean}`t1 t2 : p` as being definitionally equal, much the
-- same way as it treats {lit}`(fun x => t) s` and {lit}`t[s/x]` as
-- definitionally equal. This is known as {deftech}_proof irrelevance_, and is
-- consistent with the interpretation in the last paragraph. It means
-- that even though we can treat proofs {lean}`t : p` as ordinary objects in
-- the language of dependent type theory, they carry no information
-- beyond the fact that {lean}`p` is true.

事实上，如果 {lean}`p : Prop` 是任何命题，Lean 的内核将任何两个元素 {lean}`t1 t2 : p` 视为定义上相等，就像它将 {lit}`(fun x => t) s` 和 {lit}`t[s/x]` 视为定义上相等一样。这被称为 {deftech}_证明无关性（proof irrelevance）_，并且与上一段中的解释一致。这意味着即使我们可以将证明 {lean}`t : p` 视为依值类型论语言中的普通对象，它们除了 {lean}`p` 为真这一事实之外不携带任何信息。

-- The two ways we have suggested thinking about the
-- {tech}[propositions-as-types] paradigm differ in a fundamental way. From the
-- constructive point of view, proofs are abstract mathematical objects
-- that are _denoted_ by suitable expressions in dependent type
-- theory. In contrast, if we think in terms of the coding trick
-- described above, then the expressions themselves do not denote
-- anything interesting. Rather, it is the fact that we can write them
-- down and check that they are well-typed that ensures that the
-- proposition in question is true. In other words, the expressions
-- _themselves_ are the proofs.

我们建议的思考 {tech}[命题即类型] 范式的两种方式在根本上有所不同。从构造主义的观点来看，证明是抽象的数学对象，由依值类型论中的适当表达式 _指称（denoted）_。相反，如果我们从上述编码技巧的角度思考，那么表达式本身并不指称任何有趣的东西。相反，正是我们可以写下它们并检查它们是否类型正确这一事实，确保了所讨论的命题为真。换句话说，表达式 _本身_ 就是证明。

-- In the exposition below, we will slip back and forth between these two
-- ways of talking, at times saying that an expression “constructs” or
-- “produces” or “returns” a proof of a proposition, and at other times
-- simply saying that it “is” such a proof. This is similar to the way
-- that computer scientists occasionally blur the distinction between
-- syntax and semantics by saying, at times, that a program “computes” a
-- certain function, and at other times speaking as though the program
-- “is” the function in question.

在下面的阐述中，我们将在这两种说法之间来回切换，有时说一个表达式“构造”或“产生”或“返回”一个命题的证明，有时只是说它“是”这样一个证明。这类似于计算机科学家偶尔模糊语法和语义之间区别的方式，有时说程序“计算”某个函数，有时又好像程序“是”所讨论的函数一样。

-- In any case, all that really matters is the bottom line. To formally
-- express a mathematical assertion in the language of dependent type
-- theory, we need to exhibit a term {lean}`p : Prop`. To _prove_ that
-- assertion, we need to exhibit a term {lean}`t : p`. Lean's task, as a
-- proof assistant, is to help us to construct such a term, {lean}`t`, and to
-- verify that it is well-formed and has the correct type.

无论如何，真正重要的是底线。为了用依值类型论的语言正式表达一个数学断言，我们需要展示一个项 {lean}`p : Prop`。为了 _证明_ 该断言，我们需要展示一个项 {lean}`t : p`。Lean 的任务，作为一个证明助手，是帮助我们构造这样一个项 {lean}`t`，并验证它的格式是否良好，类型是否正确。

-- # Working with Propositions as Types
# 使用命题作为类型
%%%
tag := "working-with-propositions-as-types"
%%%

-- In the {tech}[propositions-as-types] paradigm, theorems involving only {lit}`→`
-- can be proved using lambda abstraction and application. In Lean, the
-- {kw}`theorem` command introduces a new theorem:

在 {tech}[命题即类型] 范式中，只涉及 {lit}`→` 的定理可以通过 lambda 抽象和应用来证明。在 Lean 中，{kw}`theorem` 命令引入了一个新的定理：

```lean
set_option linter.unusedVariables false
---
variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
```

-- Compare this proof to the expression {lean}`fun x : α => fun y : β => x`
-- of type {lean}`α → β → α`, where {lean}`α` and {lean}`β` are data types.
-- This describes the function that takes arguments {leanRef}`x` and {leanRef}`y`
-- of type {lean}`α` and {lean}`β`, respectively, and returns {leanRef}`x`.
-- The proof of {lean}`t1` has the same form, the only difference being that
-- {lean}`p` and {lean}`q` are elements of {lean}`Prop` rather than {lean}`Type`.
-- Intuitively, our proof of
-- {lean}`p → q → p` assumes {lean}`p` and {lean}`q` are true, and uses the first
-- hypothesis (trivially) to establish that the conclusion, {lean}`p`, is
-- true.

将此证明与类型为 {lean}`α → β → α` 的表达式 {lean}`fun x : α => fun y : β => x` 进行比较，其中 {lean}`α` 和 {lean}`β` 是数据类型。这描述了分别接受类型为 {lean}`α` 和 {lean}`β` 的参数 {leanRef}`x` 和 {leanRef}`y` 并返回 {leanRef}`x` 的函数。{lean}`t1` 的证明具有相同的形式，唯一的区别是 {lean}`p` 和 {lean}`q` 是 {lean}`Prop` 的元素，而不是 {lean}`Type` 的元素。直观地说，我们对 {lean}`p → q → p` 的证明假设 {lean}`p` 和 {lean}`q` 为真，并使用第一个假设（平凡地）建立结论 {lean}`p` 为真。

-- Note that the {kw}`theorem` command is really a version of the
-- {kw}`def` command: under the propositions and types
-- correspondence, proving the theorem {lean}`p → q → p` is really the same
-- as defining an element of the associated type. To the kernel type
-- checker, there is no difference between the two.

请注意，{kw}`theorem` 命令实际上是 {kw}`def` 命令的一个版本：在命题和类型对应下，证明定理 {lean}`p → q → p` 实际上与定义关联类型的元素是一样的。对于内核类型检查器，这两者之间没有区别。

-- There are a few pragmatic differences between definitions and
-- theorems, however. In normal circumstances, it is never necessary to
-- unfold the “definition” of a theorem; by {tech}[proof irrelevance], any two
-- proofs of that theorem are definitionally equal. Once the proof of a
-- theorem is complete, typically we only need to know that the proof
-- exists; it doesn't matter what the proof is. In light of that fact,
-- Lean tags proofs as _irreducible_, which serves as a hint to the
-- parser (more precisely, the _elaborator_) that there is generally no
-- need to unfold them when processing a file. In fact, Lean is generally
-- able to process and check proofs in parallel, since assessing the
-- correctness of one proof does not require knowing the details of
-- another. Additionally, {ref "variables-and-sections"}[section variables]
-- that are referred to in the body of a definition are automatically added as
-- parameters, but only the variables referred to in a theorem's type are added.
-- This is because the way in which a statement is proved should not influence
-- the statement that is being proved.

然而，定义和定理之间有一些实用的区别。正常情况下，永远没有必要展开一个定理的“定义”；通过 {tech}[证明无关性]，该定理的任何两个证明在定义上都是相等的。一旦一个定理的证明完成，通常我们只需要知道该证明的存在；证明是什么并不重要。鉴于这一事实，Lean 将证明标记为 _不可还原（irreducible）_，作为对解析器（更确切地说，是 _繁饰器（elaborator）_）的提示，在处理文件时一般不需要展开它。事实上，Lean 通常能够并行地处理和检查证明，因为评估一个证明的正确性不需要知道另一个证明的细节。此外，在定义体中引用的 {ref "variables-and-sections"}[章节变量] 会自动添加为参数，但只有在定理类型中引用的变量才会被添加。这是因为证明陈述的方式不应影响正在证明的陈述。

-- As with definitions, the {kw}`#print` command will show you the proof of
-- a theorem:

和定义一样，{kw}`#print` 命令可以展示一个定理的证明：

```lean
set_option linter.unusedVariables false
variable {p : Prop}
variable {q : Prop}
------
theorem t1 : p → q → p := fun hp : p => fun hq : q => hp

#print t1 -- theorem t1 : ∀ {p q : Prop}, p → q → p := fun {p q} hp hq => hp
```

-- Notice that the lambda abstractions {leanRef}`hp : p` and {leanRef}`hq : q` can be
-- viewed as temporary assumptions in the proof of {lean}`t1`.  Lean also
-- allows us to specify the type of the final term {leanRef}`hp`, explicitly,
-- with a {kw}`show` statement:

请注意，lambda 抽象 {leanRef}`hp : p` 和 {leanRef}`hq : q` 可以被视为 {lean}`t1` 证明中的临时假设。Lean 还允许我们使用 {kw}`show` 语句显式指定最终项 {leanRef}`hp` 的类型：

```lean
set_option linter.unusedVariables false
variable {p : Prop}
variable {q : Prop}
------
theorem t1 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp
```

-- Adding such extra information can improve the clarity of a proof and
-- help detect errors when writing a proof. The {kw}`show` command does
-- nothing more than annotate the type, and, internally, all the
-- presentations of {leanRef}`t1` that we have seen produce the same term.

添加此类额外信息可以提高证明的清晰度，并有助于在编写证明时检测错误。{kw}`show` 命令除了注释类型外什么也不做，在内部，我们看到的所有 {leanRef}`t1` 的表示都会产生相同的项。

-- As with ordinary definitions, we can move the lambda-abstracted
-- variables to the left of the colon:

与普通定义一样，我们可以将 lambda 抽象变量移到冒号左侧：

```lean
set_option linter.unusedVariables false
variable {p : Prop}
variable {q : Prop}
------
theorem t1 (hp : p) (hq : q) : p := hp

#print t1    -- theorem t1 : ∀ {p q : Prop}, p → q → p := fun {p q} hp hq => hp
```

-- We can use the theorem {leanRef}`t1` just as a function application:

我们可以像函数应用一样使用定理 {leanRef}`t1`：

```lean
set_option linter.unusedVariables false
variable {p : Prop}
variable {q : Prop}
------
theorem t1 (hp : p) (hq : q) : p := hp

axiom hp : p

theorem t2 : q → p := t1 hp
```

-- The {kw}`axiom` declaration postulates the existence of an
-- element of the given type and may compromise logical consistency. For
-- example, we can use it to postulate that the empty type {lean}`False` has an
-- element:

{kw}`axiom` 声明假设给定类型的元素存在，这可能会损害逻辑一致性。例如，我们可以使用它来假设空类型 {lean}`False` 有一个元素：

```lean
axiom unsound : False
-- Everything follows from false
theorem ex : 1 = 0 :=
  False.elim unsound
```

:::setup
```
variable {p q : Prop} (hp : p) {t1 : p → q → p}
```
-- Declaring an “axiom” {lean}`hp : p` is tantamount to declaring that {lean}`p`
-- is true, as witnessed by {lean}`hp`. Applying the theorem
-- {lean}`t1 : p → q → p` to the fact {lean}`hp : p` that {lean}`p` is true yields the theorem
-- {lean}`t1 hp : q → p`.

声明“公理” {lean}`hp : p` 等同于声明 {lean}`p` 为真，由 {lean}`hp` 见证。将定理 {lean}`t1 : p → q → p` 应用于 {lean}`p` 为真这一事实 {lean}`hp : p`，得到定理 {lean}`t1 hp : q → p`。

:::

-- Recall that we can also write theorem {leanRef}`t1` as follows:

回想一下，我们也可以将定理 {leanRef}`t1` 写成如下形式：

```lean
set_option linter.unusedVariables false
------
theorem t1 {p q : Prop} (hp : p) (hq : q) : p := hp

#print t1
```

-- The type of {leanRef}`t1` is now {lean}`∀ {p q : Prop}, p → q → p`. We can read
-- this as the assertion “for every pair of propositions {lean}`p`{lit}` `{lean}`q`, we have
-- {lean}`p → q → p`.” For example, we can move all parameters to the right
-- of the colon:

{leanRef}`t1` 的类型现在是 {lean}`∀ {p q : Prop}, p → q → p`。我们可以将其读作断言“对于每一对命题 {lean}`p`{lit}` `{lean}`q`，我们有 {lean}`p → q → p`。”例如，我们可以将所有参数移到冒号右侧：

```lean
set_option linter.unusedVariables false
------
theorem t1 : ∀ {p q : Prop}, p → q → p :=
  fun {p q : Prop} (hp : p) (hq : q) => hp
```

-- If {lean}`p` and {lean}`q` have been declared as {ref "variables-and-sections"}[variables], Lean will
-- generalize them for us automatically:

如果 {lean}`p` 和 {lean}`q` 已被声明为 {ref "variables-and-sections"}[变量]，Lean 会自动为我们泛化它们：

```lean
variable {p q : Prop}

theorem t1 : p → q → p := fun (hp : p) (hq : q) => hp
```

-- When we generalize {leanRef}`t1` in such a way, we can then apply it to
-- different pairs of propositions, to obtain different instances of the
-- general theorem.

当我们以这种方式泛化 {leanRef}`t1` 时，我们就可以将它应用于不同的命题对，从而得到一般定理的不同实例。

```lean
set_option linter.unusedVariables false
------
theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp

variable (p q r s : Prop)

#check t1 p q                -- t1 p q : p → q → p
#check t1 r s                -- t1 r s : r → s → r
#check t1 (r → s) (s → r)    -- t1 (r → s) (s → r) : (r → s) → (s → r) → r → s

variable (h : r → s)

#check t1 (r → s) (s → r) h  -- t1 (r → s) (s → r) h : (s → r) → r → s
```

-- Once again, using the {tech}[propositions-as-types] correspondence, the
-- variable {leanRef}`h` of type {leanRef}`r → s` can be viewed as the hypothesis, or
-- premise, that {leanRef}`r → s` holds.

同样，使用 {tech}[命题即类型] 对应，类型为 {leanRef}`r → s` 的变量 {leanRef}`h` 可以看作是 {leanRef}`r → s` 成立的假设或前提。

-- As another example, let us consider the composition function discussed
-- in the last chapter, now with propositions instead of types.

作为另一个例子，让我们考虑上一章讨论的组合函数，现在用命题代替类型。

```lean
variable (p q r s : Prop)

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)
```

-- As a theorem of propositional logic, what does {leanRef}`t2` say?

作为命题逻辑的定理，{leanRef}`t2` 说了什么？

-- Note that it is often useful to use numeric Unicode subscripts,
-- entered as {kbd}`\0`, {kbd}`\1`, {kbd}`\2`, ..., for hypotheses, as we did in
-- this example.

请注意，使用数字 Unicode 下标（输入为 {kbd}`\0`、{kbd}`\1`、{kbd}`\2` 等）作为假设通常很有用，就像我们在本例中所做的那样。

-- # Propositional Logic
# 命题逻辑
%%%
tag := "propositional-logic"
%%%

-- Lean defines all the standard logical connectives and notation. The propositional connectives come with the following notation:

Lean 定义了所有标准的逻辑连接词和符号。命题连接词具有以下符号：

:::table +header
*
 * ASCII
 * Unicode
 * Editor shortcut
 * Definition

*
 * {lean}`True`
 * {empty}[]
 * {empty}[]
 * {lean}`True`

*
 * {lean}`False`
 * {empty}[]
 * {empty}[]
 * {lean}`False`

*
 * {lean}`Not`
 * {lit}`¬`
 * {kbd}`\not`, {kbd}`\neg`
 * {lean}`Not`

*
 * {lit}`/\`
 * {lit}`∧`
 * {kbd}`\and`
 * {lean}`And`

*
 * {lit}`\/`
 * {lit}`∨`
 * {kbd}`\or`
 * {lean}`Or`

*
 * {lit}`->`
 * {lit}`→`
 * {kbd}`\to`, {kbd}`\r`, {kbd}`\imp`
 * {empty}[]

*
 * {lit}`<->`
 * {lit}`↔`
 * {kbd}`\iff`, {kbd}`\lr`
 * {lean}`Iff`

:::

-- They all take values in {lean}`Prop`.

它们都取 {lean}`Prop` 中的值。

```lean
variable (p q : Prop)

#check p → q → p ∧ q

#check ¬p → p ↔ False

#check p ∨ q → q ∨ p
```

:::setup
```
variable (p q r a b c d e : Prop)
```
-- The order of operations is as follows: unary negation {lit}`¬` binds most
-- strongly, then {lit}`∧`, then {lit}`∨`, then {lit}`→`, and finally {lit}`↔`. For
-- example, {lean}`a ∧ b → c ∨ d ∧ e` means {lean}`(a ∧ b) → (c ∨ (d ∧ e))`.
-- Remember that {lit}`→` associates to the right (nothing changes
-- now that the arguments are elements of {lean}`Prop`, instead of some other
-- {lean}`Type`), as do the other binary connectives. So if we have
-- {lean}`p q r : Prop`, the expression {lean}`p → q → r` reads “if {lean}`p`, then if {lean}`q`,
-- then {lean}`r`.” This is just the “curried” form of {lean}`p ∧ q → r`.

运算顺序如下：一元否定 {lit}`¬` 结合力最强，然后是 {lit}`∧`，然后是 {lit}`∨`，然后是 {lit}`→`，最后是 {lit}`↔`。例如，{lean}`a ∧ b → c ∨ d ∧ e` 意味着 {lean}`(a ∧ b) → (c ∨ (d ∧ e))`。请记住，{lit}`→` 是右结合的（现在参数是 {lean}`Prop` 的元素，而不是其他 {lean}`Type`，这一点没有改变），其他二元连接词也是如此。因此，如果我们有 {lean}`p q r : Prop`，表达式 {lean}`p → q → r` 读作“如果 {lean}`p`，那么如果 {lean}`q`，那么 {lean}`r`。”这只是 {lean}`p ∧ q → r` 的“柯里化”形式。

:::

-- In the last chapter we observed that lambda abstraction can be viewed
-- as an “introduction rule” for {lit}`→`. In the current setting, it shows
-- how to “introduce” or establish an implication. Application can be
-- viewed as an “elimination rule,” showing how to “eliminate” or use an
-- implication in a proof. The other propositional connectives are
-- defined in Lean's library, and are automatically imported. Each connective
-- comes with its canonical introduction and elimination rules.

在上一章中，我们观察到 lambda 抽象可以被视为 {lit}`→` 的“引入规则”。在当前的设置中，它展示了如何“引入”或建立蕴涵。应用可以被视为“消去规则”，展示了如何在证明中“消去”或使用蕴涵。其他命题连接词在 Lean 的库中定义，并自动导入。每个连接词都有其规范的引入和消去规则。

-- ## Conjunction
## 合取
%%%
tag := "conjunction"
%%%

:::setup
```
variable (p q : Prop) (h1 : p) (h2 : q)
```

-- The expression {lean}`And.intro h1 h2` builds a proof of {lean}`p ∧ q` using
-- proofs {lean}`h1 : p` and {lean}`h2 : q`. It is common to describe
-- {lean}`And.intro` as the _and-introduction_ rule. In the next example we
-- use {lean}`And.intro` to create a proof of {lean}`p → q → p ∧ q`.
表达式 {lean}`And.intro h1 h2` 是 {lean}`p ∧ q` 的证明，它使用了 {lean}`h1 : p` 和 {lean}`h2 : q` 的证明。通常把 {lean}`And.intro` 称为*合取引入*规则。下面的例子我们使用 {lean}`And.intro` 来创建 {lean}`p → q → p ∧ q` 的证明。

:::

```lean
variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

#check fun (hp : p) (hq : q) => And.intro hp hq
```

-- The {kw}`example` command states a theorem without naming it or storing
-- it in the permanent context. Essentially, it just checks that the
-- given term has the indicated type. It is convenient for illustration,
-- and we will use it often.

{kw}`example` 命令声明了一个没有名字也不会永久保存的定理。本质上，它只是检查给定项是否具有指定的类型。它便于说明，我们将经常使用它。

:::setup
```
variable (p q : Prop) (h : p ∧ q)
```
-- The expression {lean}`And.left h` creates a proof of {lean}`p` from a proof
-- {lean}`h : p ∧ q`. Similarly, {lean}`And.right h` is a proof of {lean}`q`. They
-- are commonly known as the left and right _and-elimination_ rules.

表达式 {lean}`And.left h` 从证明 {lean}`h : p ∧ q` 创建 {lean}`p` 的证明。类似地，{lean}`And.right h` 是 {lean}`q` 的证明。它们常被称为左和右 _与消去（and-elimination）_ 规则。

:::

```lean
variable (p q : Prop)

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h
```

-- We can now prove {lean}`p ∧ q → q ∧ p` with the following proof term.

我们现在可以用以下证明项证明 {lean}`p ∧ q → q ∧ p`。

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)
```

:::setup
```
variable (p q : Prop) (hp : p) (hq : q) (α β : Type) (a : α) (b : β)

```
-- Notice that and-introduction and and-elimination are similar to the
-- pairing and projection operations for the Cartesian product. The
-- difference is that given {lean}`hp : p` and {lean}`hq : q`, {lean}`And.intro hp hq` has type
-- {lean}`p ∧ q : Prop`, while given {lean}`a : α` and {lean}`b : β`, {lean}`Prod.mk a b` has type
-- {lean}`α × β : Type`. {lean}`Prod` cannot be used with {lean}`Prop`s, and {lean}`And` cannot be used with {lean}`Type`s.
-- The similarity between {lit}`∧` and {lit}`×` is another instance
-- of the {tech}[Curry-Howard isomorphism], but in contrast to implication and
-- the function space constructor, {lit}`∧` and {lit}`×` are treated separately
-- in Lean. With the analogy, however, the proof we have just constructed
-- is similar to a function that swaps the elements of a pair.

请注意，与引入和与消去类似于笛卡尔积的配对和投影操作。区别在于，给定 {lean}`hp : p` 和 {lean}`hq : q`，{lean}`And.intro hp hq` 具有类型 {lean}`p ∧ q : Prop`，而给定 {lean}`a : α` 和 {lean}`b : β`，{lean}`Prod.mk a b` 具有类型 {lean}`α × β : Type`。{lean}`Prod` 不能用于 {lean}`Prop`，{lean}`And` 不能用于 {lean}`Type`。{lit}`∧` 和 {lit}`×` 之间的相似性是 {tech}[柯里-霍华德同构] 的另一个实例，但与蕴涵和函数空间构造子不同，{lit}`∧` 和 {lit}`×` 在 Lean 中是分开处理的。然而，通过类比，我们刚刚构造的证明类似于交换一对中的元素的函数。

-- We will see in {ref "structures-and-records"}[Structures and Records] that certain
-- types in Lean are _structures_, which is to say, the type is defined
-- with a single canonical _constructor_ which builds an element of the
-- type from a sequence of suitable arguments. For every {lean}`p q : Prop`,
-- {lean}`p ∧ q` is an example: the canonical way to construct an element is
-- to apply {lean}`And.intro` to suitable arguments {lean}`hp : p` and
-- {lean}`hq : q`. Lean allows us to use _anonymous constructor_ notation
-- {lit}`⟨arg1, arg2, ...⟩` in situations like these, when the relevant type is an
-- inductive type and can be inferred from the context. In particular, we
-- can often write {lean (type := "p ∧ q")}`⟨hp, hq⟩` instead of {lean}`And.intro hp hq`:

我们将在 {ref "structures-and-records"}[结构体和记录] 中看到，Lean 中的某些类型是 _结构体（structures）_，也就是说，该类型是用单个规范的 _构造子（constructor）_ 定义的，该构造子从一系列合适的参数构建该类型的一个元素。对于每个 {lean}`p q : Prop`，{lean}`p ∧ q` 就是一个例子：构造一个元素的规范方法是将 {lean}`And.intro` 应用于合适的参数 {lean}`hp : p` 和 {lean}`hq : q`。Lean 允许我们在这种情况下使用 _匿名构造子（anonymous constructor）_ 表示法 {lit}`⟨arg1, arg2, ...⟩`，当相关类型是归纳类型并可以从上下文推断时。特别地，我们经常可以写 {lean (type := "p ∧ q")}`⟨hp, hq⟩` 而不是 {lean}`And.intro hp hq`：

:::

```lean
variable (p q : Prop)
variable (hp : p) (hq : q)

#check (⟨hp, hq⟩ : p ∧ q)
```

-- These angle brackets are obtained by typing {kbd}`\<` and {kbd}`\>`, respectively.

这些尖括号分别通过输入 {kbd}`\<` 和 {kbd}`\>` 获得。

:::setup
```
inductive Foo where | mk
inductive Bar where | mk : Foo → Bar
variable (e : Foo)
def Foo.bar (x : Foo) : Bar := .mk x
```
-- Lean provides another useful syntactic gadget. Given an expression
-- {lean}`e` of an inductive type {lean}`Foo` (possibly applied to some
-- arguments), the notation {lean}`e.bar` is shorthand for {lean}`Foo.bar e`.
-- This provides a convenient way of accessing functions without opening
-- a namespace.  For example, the following two expressions mean the same
-- thing:

Lean 提供了另一个有用的语法小工具。给定一个归纳类型 {lean}`Foo` 的表达式 {lean}`e`（可能应用于一些参数），符号 {lean}`e.bar` 是 {lean}`Foo.bar e` 的简写。这为访问函数提供了一种方便的方式，而无需打开命名空间。例如，以下两个表达式的意思是相同的：

:::

```lean
variable (xs : List Nat)

#check List.length xs

#check xs.length
```

:::setup
```
variable (p q : Prop) (h : p ∧ q)
```

-- As a result, given {lean}`h : p ∧ q`, we can write {lean}`h.left` for
-- {lean}`And.left h` and {lean}`h.right` for {lean}`And.right h`. We can therefore
-- rewrite the sample proof above conveniently as follows:

因此，给定 {lean}`h : p ∧ q`，我们可以写 {lean}`h.left` 来表示 {lean}`And.left h`，用 {lean}`h.right` 来表示 {lean}`And.right h`。因此我们可以方便地将上面的示例证明重写如下：

:::


```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩
```

-- There is a fine line between brevity and obfuscation, and omitting
-- information in this way can sometimes make a proof harder to read. But
-- for straightforward constructions like the one above, when the type of
-- {leanRef}`h` and the goal of the construction are salient, the notation is
-- clean and effective.

简洁和晦涩之间只有一线之隔，以这种方式省略信息有时会使证明更难阅读。但对于像上面这样直截了当的构造，当 {leanRef}`h` 的类型和构造的目标很显著时，这种表示法是干净有效的。

-- It is common to iterate constructions like “And.” Lean also allows you
-- to flatten nested constructors that associate to the right, so that
-- these two proofs are equivalent:

迭代像“And”这样的构造是很常见的。Lean 还允许你展平右结合的嵌套构造子，因此这两个证明是等价的：

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, ⟨h.left, h.right⟩⟩

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, h.left, h.right⟩
```

-- This is often useful as well.

这也通常很有用。

-- ## Disjunction
## 析取
%%%
tag := "disjunction"
%%%

:::setup
```
variable (p q : Prop) (hp : p) (hq : q)
```

-- The expression {lean}`Or.intro_left q hp` creates a proof of {lean}`p ∨ q`
-- from a proof {lean}`hp : p`. Similarly, {lean}`Or.intro_right p hq` creates a
-- proof for {lean}`p ∨ q` using a proof {lean}`hq : q`. These are the left and
-- right _or-introduction_ rules.

表达式 {lean}`Or.intro_left q hp` 从证明 {lean}`hp : p` 创建 {lean}`p ∨ q` 的证明。类似地，{lean}`Or.intro_right p hq` 使用证明 {lean}`hq : q` 创建 {lean}`p ∨ q` 的证明。这些是左和右 _或引入（or-introduction）_ 规则。

:::

```lean
variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq
```

:::setup
```
variable (p q r : Prop) (hpq : p ∨ q) (hpr : p → r) (hqr : q → r)
```
-- The _or-elimination_ rule is slightly more complicated. The idea is
-- that we can prove {lean}`r` from {lean}`p ∨ q`, by showing that {lean}`r` follows
-- from {lean}`p` and that {lean}`r` follows from {lean}`q`.  In other words, it is a
-- proof by cases. In the expression {lean}`Or.elim hpq hpr hqr`, {lean}`Or.elim`
-- takes three arguments, {lean}`hpq : p ∨ q`, {lean}`hpr : p → r` and
-- {lean}`hqr : q → r`, and produces a proof of {lean}`r`. In the following example, we use
-- {lean}`Or.elim` to prove {lean}`p ∨ q → q ∨ p`.

_或消去（or-elimination）_ 规则稍微复杂一些。其思想是，我们可以通过证明 {lean}`r` 从 {lean}`p` 推出以及 {lean}`r` 从 {lean}`q` 推出，来从 {lean}`p ∨ q` 证明 {lean}`r`。换句话说，这是一个分情况证明。在表达式 {lean}`Or.elim hpq hpr hqr` 中，{lean}`Or.elim` 接受三个参数：{lean}`hpq : p ∨ q`、{lean}`hpr : p → r` 和 {lean}`hqr : q → r`，并产生 {lean}`r` 的证明。在以下示例中，我们使用 {lean}`Or.elim` 来证明 {lean}`p ∨ q → q ∨ p`。

:::

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)
```

-- In most cases, the first argument of {lean}`Or.intro_right` and
-- {lean}`Or.intro_left` can be inferred automatically by Lean. Lean
-- therefore provides {lean}`Or.inr` and {lean}`Or.inl` which can be viewed as
-- shorthand for {lean}`Or.intro_right _` and {lean}`Or.intro_left _`. Thus the
-- proof term above could be written more concisely:

在大多数情况下，{lean}`Or.intro_right` 和 {lean}`Or.intro_left` 的第一个参数可以由 Lean 自动推断出来。因此，Lean 提供了 {lean}`Or.inr` 和 {lean}`Or.inl`，它们可以被视为 {lean}`Or.intro_right _` 和 {lean}`Or.intro_left _` 的简写。因此，上面的证明项可以写得更简洁：

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)
```

-- Notice that there is enough information in the full expression for
-- Lean to infer the types of {leanRef}`hp` and {leanRef}`hq` as well.  But using the
-- type annotations in the longer version makes the proof more readable,
-- and can help catch and debug errors.

请注意，完整表达式中有足够的信息供 Lean 推断 {leanRef}`hp` 和 {leanRef}`hq` 的类型。但是，在较长版本中使用类型注释可以使证明更具可读性，并有助于捕获和调试错误。

:::setup
```
variable (h : p ∨ q)
```
-- Because {lean}`Or` has two constructors, we cannot use anonymous
-- constructor notation. But we can still write {lean}`h.elim` instead of
-- {lean}`Or.elim h`:

因为 {lean}`Or` 有两个构造子，所以我们不能使用匿名构造子表示法。但我们仍然可以写 {lean}`h.elim` 而不是 {lean}`Or.elim h`：

:::

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)
```

-- Once again, you should exercise judgment as to whether such
-- abbreviations enhance or diminish readability.

再一次，你应该判断这些缩写是增强还是降低了可读性。

-- ## Negation and Falsity
## 否定与假
%%%
tag := "negation-and-falsity"
%%%

:::setup
```
variable (p q : Prop) (hnp : ¬ p) (hp : p)
```
-- Negation, {lean}`¬p`, is actually defined to be {lean}`p → False`, so we
-- obtain {lean}`¬p` by deriving a contradiction from {lean}`p`. Similarly, the
-- expression {lean}`hnp hp` produces a proof of {lean}`False` from {lean}`hp : p`
-- and {lean}`hnp : ¬p`. The next example uses both these rules to produce a
-- proof of {lean}`(p → q) → ¬q → ¬p`. (The symbol {lit}`¬` is produced by
-- typing {kbd}`\not` or {kbd}`\neg`.)

否定 {lean}`¬p` 实际上定义为 {lean}`p → False`，所以我们通过从 {lean}`p` 导出一个矛盾来获得 {lean}`¬p`。类似地，表达式 {lean}`hnp hp` 从 {lean}`hp : p` 和 {lean}`hnp : ¬p` 产生一个 {lean}`False` 的证明。下一个例子使用这两个规则来产生 {lean}`(p → q) → ¬q → ¬p` 的证明。（符号 {lit}`¬` 通过输入 {kbd}`\not` 或 {kbd}`\neg` 产生。）

:::

```lean
variable (p q : Prop)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)
```

-- The connective {lean}`False` has a single elimination rule,
-- {lean}`False.elim`, which expresses the fact that anything follows from a
-- contradiction. This rule is sometimes called _ex falso_ (short for _ex
-- falso sequitur quodlibet_), or the _principle of explosion_.

连接词 {lean}`False` 只有一个消去规则 {lean}`False.elim`，它表达了一个事实，即任何事物都可以从矛盾中推出。这个规则有时被称为 _ex falso_（_ex falso sequitur quodlibet_ 的缩写），或 _爆炸原理（principle of explosion）_。

```lean
variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
```

-- The arbitrary fact, {lean}`q`, that follows from falsity is an implicit
-- argument in {lean}`False.elim` and is inferred automatically. This
-- pattern, deriving an arbitrary fact from contradictory hypotheses, is
-- quite common, and is represented by {lean}`absurd`.

从虚假中推出的任意事实 {lean}`q` 是 {lean}`False.elim` 中的隐式参数，并且会自动推断出来。这种从矛盾假设中推导出任意事实的模式非常常见，并由 {lean}`absurd` 表示。

```lean
variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := absurd hp hnp
```

-- Here, for example, is a proof of {lean}`¬p → q → (q → p) → r`:

例如，这里是 {lean}`¬p → q → (q → p) → r` 的证明：

```lean
variable (p q r : Prop)

example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp
```

-- Incidentally, just as {lean}`False` has only an elimination rule, {lean}`True`
-- has only an introduction rule, {lean}`True.intro : True`.  In other words,
-- {lean}`True` is simply true, and has a canonical proof, {lean}`True.intro`.

顺便说一句，就像 {lean}`False` 只有一个消去规则一样，{lean}`True` 只有一个引入规则 {lean}`True.intro : True`。换句话说，{lean}`True` 仅仅是真的，并且有一个规范的证明 {lean}`True.intro`。

-- ## Logical Equivalence
## 逻辑等价
%%%
tag := "logical-equivalence"
%%%

:::setup

```
variable (p q : Prop) (h1 : p → q) (h2 : q → p) (h : p ↔ q)
```
-- The expression {lean}`Iff.intro h1 h2` produces a proof of {lean}`p ↔ q` from
-- {lean}`h1 : p → q` and {lean}`h2 : q → p`.  The expression {lean}`Iff.mp h`
-- produces a proof of {lean}`p → q` from {lean}`h : p ↔ q`. Similarly,
-- {lean}`Iff.mpr h` produces a proof of {lean}`q → p` from {lean}`h : p ↔ q`. Here is a proof
-- of {lean}`p ∧ q ↔ q ∧ p`:

表达式 {lean}`Iff.intro h1 h2` 从 {lean}`h1 : p → q` 和 {lean}`h2 : q → p` 产生 {lean}`p ↔ q` 的证明。表达式 {lean}`Iff.mp h` 从 {lean}`h : p ↔ q` 产生 {lean}`p → q` 的证明。类似地，{lean}`Iff.mpr h` 从 {lean}`h : p ↔ q` 产生 {lean}`q → p` 的证明。这是 {lean}`p ∧ q ↔ q ∧ p` 的证明：

:::
```lean
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q    -- and_swap p q : p ∧ q ↔ q ∧ p

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h
```

-- We can use the anonymous constructor notation to construct a proof of
-- {lean}`p ↔ q` from proofs of the forward and backward directions, and we
-- can also use {lit}`.` notation with {lit}`mp` and {lit}`mpr`. The previous
-- examples can therefore be written concisely as follows:

我们可以使用匿名构造子表示法从前向和后向的证明构造 {lean}`p ↔ q` 的证明，我们也可以对 {lit}`mp` 和 {lit}`mpr` 使用 {lit}`.` 表示法。因此，前面的示例可以简洁地写成如下形式：

```lean
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h
```

-- # Introducing Auxiliary Subgoals
# 引入辅助子目标
%%%
tag := "introducing-auxiliary-subgoals"
%%%

-- This is a good place to introduce another device Lean offers to help
-- structure long proofs, namely, the {kw}`have` construct, which
-- introduces an auxiliary subgoal in a proof. Here is a small example,
-- adapted from the last section:

这是一个介绍 Lean 提供的另一个帮助构建长证明的工具的好地方，即 {kw}`have` 构造，它在证明中引入了一个辅助子目标。这是一个改编自上一节的小例子：

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp
```

:::setup
```
variable (p q : Prop) (s : p) (t : q)
```
-- Internally, the expression {lean}`have h : p := s; t` produces the term
-- {lean}`(fun (h : p) => t) s`. In other words, {lean}`s` is a proof of {lean}`p`,
-- {lean}`t` is a proof of the desired conclusion assuming {leanRef}`h : p`, and the
-- two are combined by a lambda abstraction and application. This simple
-- device is extremely useful when it comes to structuring long proofs,
-- since we can use intermediate {kw}`have`'s as stepping stones leading to
-- the final goal.

在内部，表达式 {lean}`have h : p := s; t` 产生项 {lean}`(fun (h : p) => t) s`。换句话说，{lean}`s` 是 {lean}`p` 的证明，{lean}`t` 是假设 {leanRef}`h : p` 的情况下所需结论的证明，两者通过 lambda 抽象和应用结合在一起。这个简单的工具在构建长证明时非常有用，因为我们可以使用中间的 {kw}`have` 作为通向最终目标的垫脚石。

:::

-- Lean also supports a structured way of reasoning backwards from a
-- goal, which models the “suffices to show” construction in ordinary
-- mathematics. The next example simply permutes the last two lines in
-- the previous proof.

Lean 还支持一种从目标向后推理的结构化方式，这模仿了普通数学中的“足以证明（suffices to show）”结构。下一个例子只是交换了前一个证明中的最后两行。

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h
```

-- Writing {leanRef}`suffices hq : q` leaves us with two goals. First, we have
-- to show that it indeed suffices to show {lean}`q`, by proving the original
-- goal of {leanRef}`q ∧ p` with the additional hypothesis {leanRef}`hq : q`. Finally,
-- we have to show {leanRef}`q`.

写下 {leanRef}`suffices hq : q` 给我们留下了两个目标。首先，我们必须证明它确实足以证明 {lean}`q`，方法是用额外的假设 {leanRef}`hq : q` 证明 {leanRef}`q ∧ p` 的原始目标。最后，我们必须证明 {leanRef}`q`。

-- # Classical Logic
# 经典逻辑
%%%
tag := "classical-logic"
%%%

-- The introduction and elimination rules we have seen so far are all
-- constructive, which is to say, they reflect a computational
-- understanding of the logical connectives based on the
-- {tech}[propositions-as-types] correspondence. Ordinary classical logic adds to
-- this the law of the excluded middle, {lean}`p ∨ ¬p`. To use this
-- principle, you have to open the classical namespace.

到目前为止，我们看到的引入和消去规则都是构造性的，也就是说，它们反映了基于 {tech}[命题即类型] 对应的逻辑连接词的计算理解。普通经典逻辑在此基础上增加了排中律，{lean}`p ∨ ¬p`。要使用这个原则，你必须打开经典命名空间。

```lean
open Classical

variable (p : Prop)

#check em p
```

:::setup
```
variable (p q RH : Prop)
```
-- Intuitively, the constructive “Or” is very strong: asserting {lean}`p ∨ q`
-- amounts to knowing which is the case. If {lean}`RH` represents the Riemann
-- hypothesis, a classical mathematician is willing to assert
-- {lean}`RH ∨ ¬RH`, even though we cannot yet assert either disjunct.

直观地说，构造性的“或”非常强：断言 {lean}`p ∨ q` 相当于知道哪种情况成立。如果 {lean}`RH` 代表黎曼猜想，经典数学家愿意断言 {lean}`RH ∨ ¬RH`，即使我们还不能断言任何一个析取项。

:::

-- One consequence of the law of the excluded middle is the principle of
-- double-negation elimination:

排中律的一个推论是双重否定消去原理：

```lean
open Classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)
```

:::setup
```
open Classical
variable (p : Prop)
theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)
```

-- Double-negation elimination allows one to prove any proposition,
-- {lean}`p`, by assuming {lean}`¬p` and deriving {lean}`False`, because that amounts
-- to proving {lean}`¬¬p`. In other words, double-negation elimination allows
-- one to carry out a proof by contradiction, something which is not
-- generally possible in constructive logic. As an exercise, you might
-- try proving the converse, that is, showing that {lean}`em` can be proved
-- from {lean}`dne`.

双重否定消去允许人们通过假设 {lean}`¬p` 并推导出 {lean}`False` 来证明任何命题 {lean}`p`，因为这相当于证明 {lean}`¬¬p`。换句话说，双重否定消去允许人们进行反证法，这在构造逻辑中通常是不可能的。作为练习，你可以尝试证明逆命题，即证明 {lean}`em` 可以从 {lean}`dne` 证明。

-- The classical axioms also give you access to additional patterns of
-- proof that can be justified by appeal to {lean}`em`.  For example, one can
-- carry out a proof by cases:

经典公理还允许你使用可以通过诉诸 {lean}`em` 来证明的其他证明模式。例如，人们可以进行分情况证明：

:::

```lean
open Classical
variable (p : Prop)

example (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)
```

-- Or you can carry out a proof by contradiction:

或者你可以进行反证法：

```lean
open Classical
variable (p : Prop)

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
     show False from h h1)
```

-- If you are not used to thinking constructively, it may take some time
-- for you to get a sense of where classical reasoning is used.  It is
-- needed in the following example because, from a constructive
-- standpoint, knowing that {lean}`p` and {lean}`q` are not both true does not
-- necessarily tell you which one is false:

如果你不习惯构造性思考，可能需要一些时间才能理解在哪里使用经典推理。在下面的例子中需要它，因为从构造性的角度来看，知道 {lean}`p` 和 {lean}`q` 不都为真并不一定告诉你哪一个为假：

```lean
open Classical
variable (p q : Prop)
------
example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr
        (show ¬q from
          fun hq : q =>
          h ⟨hp, hq⟩))
    (fun hp : ¬p =>
      Or.inl hp)
```

-- We will see later that there _are_ situations in constructive logic
-- where principles like excluded middle and double-negation elimination
-- are permissible, and Lean supports the use of classical reasoning in
-- such contexts without relying on excluded middle.

我们稍后将看到，在构造逻辑中 _确实_ 存在允许排中律和双重否定消去等原则的情况，并且 Lean 支持在这种情况下使用经典推理而不依赖于排中律。

-- The full list of axioms that are used in Lean to support classical
-- reasoning are discussed in {ref "axioms-and-computation"}[Axioms and Computation].

Lean 中用于支持经典推理的完整公理列表在 {ref "axioms-and-computation"}[公理与计算] 中讨论。

-- # Examples of Propositional Validities
# 命题有效性的例子
%%%
tag := "examples-of-propositional-validities"
%%%

:::setup
```
variable (p q r s : Prop)
```

-- Lean's standard library contains proofs of many valid statements of
-- propositional logic, all of which you are free to use in proofs of
-- your own. The following list includes a number of common identities.

Lean 的标准库包含许多命题逻辑有效陈述的证明，你可以自由地在自己的证明中使用所有这些证明。以下列表包括许多常见的恒等式。

-- Commutativity:

交换律：

-- 1. {lean}`p ∧ q ↔ q ∧ p`
-- 2. {lean}`p ∨ q ↔ q ∨ p`

1. {lean}`p ∧ q ↔ q ∧ p`
2. {lean}`p ∨ q ↔ q ∨ p`

-- Associativity:

结合律：

-- 3. {lean}`(p ∧ q) ∧ r ↔ p ∧ (q ∧ r)`
-- 4. {lean}`(p ∨ q) ∨ r ↔ p ∨ (q ∨ r)`

3. {lean}`(p ∧ q) ∧ r ↔ p ∧ (q ∧ r)`
4. {lean}`(p ∨ q) ∨ r ↔ p ∨ (q ∨ r)`

-- Distributivity:

分配律：

-- 5. {lean}`p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)`
-- 6. {lean}`p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)`

5. {lean}`p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)`
6. {lean}`p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)`

-- Other properties:

其他性质：

-- 7. {lean}`(p → (q → r)) ↔ (p ∧ q → r)`
-- 8. {lean}`((p ∨ q) → r) ↔ (p → r) ∧ (q → r)`
-- 9. {lean}`¬(p ∨ q) ↔ ¬p ∧ ¬q`
-- 10. {lean}`¬p ∨ ¬q → ¬(p ∧ q)`
-- 11. {lean}`¬(p ∧ ¬p)`
-- 12. {lean}`p ∧ ¬q → ¬(p → q)`
-- 13. {lean}`¬p → (p → q)`
-- 14. {lean}`(¬p ∨ q) → (p → q)`
-- 15. {lean}`p ∨ False ↔ p`
-- 16. {lean}`p ∧ False ↔ False`
-- 17. {lean}`¬(p ↔ ¬p)`
-- 18. {lean}`(p → q) → (¬q → ¬p)`

7. {lean}`(p → (q → r)) ↔ (p ∧ q → r)`
8. {lean}`((p ∨ q) → r) ↔ (p → r) ∧ (q → r)`
9. {lean}`¬(p ∨ q) ↔ ¬p ∧ ¬q`
10. {lean}`¬p ∨ ¬q → ¬(p ∧ q)`
11. {lean}`¬(p ∧ ¬p)`
12. {lean}`p ∧ ¬q → ¬(p → q)`
13. {lean}`¬p → (p → q)`
14. {lean}`(¬p ∨ q) → (p → q)`
15. {lean}`p ∨ False ↔ p`
16. {lean}`p ∧ False ↔ False`
17. {lean}`¬(p ↔ ¬p)`
18. {lean}`(p → q) → (¬q → ¬p)`

-- These require classical reasoning:

这些需要经典推理：

-- 19. {lean}`(p → r ∨ s) → ((p → r) ∨ (p → s))`
-- 20. {lean}`¬(p ∧ q) → ¬p ∨ ¬q`
-- 21. {lean}`¬(p → q) → p ∧ ¬q`
-- 22. {lean}`(p → q) → (¬p ∨ q)`
-- 23. {lean}`(¬q → ¬p) → (p → q)`
-- 24. {lean}`p ∨ ¬p`
-- 25. {lean}`(((p → q) → p) → p)`

19. {lean}`(p → r ∨ s) → ((p → r) ∨ (p → s))`
20. {lean}`¬(p ∧ q) → ¬p ∨ ¬q`
21. {lean}`¬(p → q) → p ∧ ¬q`
22. {lean}`(p → q) → (¬p ∨ q)`
23. {lean}`(¬q → ¬p) → (p → q)`
24. {lean}`p ∨ ¬p`
25. {lean}`(((p → q) → p) → p)`

-- The {lean}`sorry` identifier magically produces a proof of anything, or
-- provides an object of any data type at all. Of course, it is unsound
-- as a proof method—for example, you can use it to prove {lean}`False`—and
-- Lean produces severe warnings when files use or import theorems
-- which depend on it. But it is very useful for building long proofs
-- incrementally. Start writing the proof from the top down, using
-- {lean}`sorry` to fill in subproofs. Make sure Lean accepts the term with
-- all the {lean}`sorry`'s; if not, there are errors that you need to
-- correct. Then go back and replace each {lean}`sorry` with an actual proof,
-- until no more remain.

{lean}`sorry` 标识符神奇地产生任何东西的证明，或者提供任何数据类型的对象。当然，作为一种证明方法，它是不可靠的（例如，你可以用它来证明 {lean}`False`）当文件使用或导入依赖于它的定理时，Lean 会产生严重的警告。但它对于增量构建长证明非常有用。从上到下开始编写证明，使用 {lean}`sorry` 填充子证明。确保 Lean 接受带有所有 {lean}`sorry` 的项；如果没有，则说明你需要更正错误。然后回去用实际的证明替换每个 {lean}`sorry`，直到没有剩余。

-- Here is another useful trick. Instead of using {lean}`sorry`, you can use
-- an underscore {lit}`_` as a placeholder. Recall this tells Lean that
-- the argument is implicit, and should be filled in automatically. If
-- Lean tries to do so and fails, it returns with an error message “don't
-- know how to synthesize placeholder,” followed by the type of
-- the term it is expecting, and all the objects and hypotheses available
-- in the context. In other words, for each unresolved placeholder, Lean
-- reports the subgoal that needs to be filled at that point. You can
-- then construct a proof by incrementally filling in these placeholders.

这里有另一个有用的技巧。你可以使用下划线 {lit}`_` 作为占位符，而不是使用 {lean}`sorry`。回想一下，这告诉 Lean 参数是隐式的，应该自动填充。如果 Lean 尝试这样做但失败了，它会返回一条错误消息“don't know how to synthesize placeholder”（不知道如何合成占位符），后面跟着它期望的项的类型，以及上下文中可用的所有对象和假设。换句话说，对于每个未解决的占位符，Lean 报告在该点需要填充的子目标。然后，你可以通过增量填充这些占位符来构造证明。

:::

-- For reference, here are two sample proofs of validities taken from the
-- list above.

作为参考，这里有两个取自上面列表的有效性证明示例。

```lean
open Classical

-- distributivity
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

-- an example that requires classical reasoning
-- 一个需要经典推理的例子
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)
```

-- # Exercises
# 练习
%%%
tag := "propositions-and-proofs-exercises"
%%%

-- Prove the following identities, replacing the {lean}`sorry` placeholders with actual proofs.

证明以下恒等式，用实际证明替换 {lean}`sorry` 占位符。

```lean
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := sorry
example : p ∨ q ↔ q ∨ p := sorry

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
```

-- Prove the following identities, replacing the {lean}`sorry` placeholders
-- with actual proofs. These require classical reasoning.

证明以下恒等式，用实际证明替换 {lean}`sorry` 占位符。这些需要经典推理。

```lean
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
```

-- Prove {lean}`¬(p ↔ ¬p)` without using classical logic.

在不使用经典逻辑的情况下证明 {lean}`¬(p ↔ ¬p)`。
