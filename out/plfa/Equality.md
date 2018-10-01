---
src       : src/plfa/Equality.lagda
title     : "Equality: Equality and equational reasoning"
layout    : page
prev      : /Relations/
permalink : /Equality/
next      : /Isomorphism/
---

<pre class="Agda">{% raw %}<a id="171" class="Keyword">module</a> <a id="178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}" class="Module">plfa.Equality</a> <a id="192" class="Keyword">where</a>{% endraw %}</pre>

Much of our reasoning has involved equality.  Given two terms `M`
and `N`, both of type `A`, we write `M ≡ N` to assert that `M` and `N`
are interchangeable.  So far we have treated equality as a primitive,
here we show how to define it as an inductive datatype.


## Imports

This chapter has no imports.  Every chapter in this book, and nearly
every module in the Agda, imports equality.  Since we define equality
here, any import would create a conflict.


## Equality

We declare equality as follows.
<pre class="Agda">{% raw %}<a id="728" class="Keyword">data</a> <a id="_≡_"></a><a id="733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">_≡_</a> <a id="737" class="Symbol">{</a><a id="738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#738" class="Bound">A</a> <a id="740" class="Symbol">:</a> <a id="742" class="PrimitiveType">Set</a><a id="745" class="Symbol">}</a> <a id="747" class="Symbol">(</a><a id="748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#748" class="Bound">x</a> <a id="750" class="Symbol">:</a> <a id="752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#738" class="Bound">A</a><a id="753" class="Symbol">)</a> <a id="755" class="Symbol">:</a> <a id="757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#738" class="Bound">A</a> <a id="759" class="Symbol">→</a> <a id="761" class="PrimitiveType">Set</a> <a id="765" class="Keyword">where</a>
  <a id="_≡_.refl"></a><a id="773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a> <a id="778" class="Symbol">:</a> <a id="780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#748" class="Bound">x</a> <a id="782" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#748" class="Bound">x</a>{% endraw %}</pre>
In other words, for any type `A` and for any `x` of type `A`, the
constructor `refl` provides evidence that `x ≡ x`. Hence, every value
is equivalent to itself, and we have no other way of showing values
are equivalent.  The definition features an asymmetry, in that the
first argument to `_≡_` is given by the parameter `x : A`, while the
second is given by an index in `A → Set`.  This follows our policy
of using parameters wherever possible.  The first argument to `_≡_`
can be a parameter because it doesn't vary, while the second must be
an index, so it can be required to be equal to the first.

We declare the precedence of equivalence as follows.
<pre class="Agda">{% raw %}<a id="1466" class="Keyword">infix</a> <a id="1472" class="Number">4</a> <a id="1474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">_≡_</a>{% endraw %}</pre>
We set the precedence of `_≡_` at level 4, the same as `_≤_`,
which means it binds less tightly than any arithmetic operator.
It associates neither to left nor right; writing `x ≡ y ≡ z`
is illegal.


## Equality is an equivalence relation

An equivalence relation is one which is reflexive, symmetric, and transitive.
Reflexivity is built-in to the definition of equivalence, via the
constructor `refl`.  It is straightforward to show symmetry.
<pre class="Agda">{% raw %}<a id="sym"></a><a id="1948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1948" class="Function">sym</a> <a id="1952" class="Symbol">:</a> <a id="1954" class="Symbol">∀</a> <a id="1956" class="Symbol">{</a><a id="1957" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1957" class="Bound">A</a> <a id="1959" class="Symbol">:</a> <a id="1961" class="PrimitiveType">Set</a><a id="1964" class="Symbol">}</a> <a id="1966" class="Symbol">{</a><a id="1967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1967" class="Bound">x</a> <a id="1969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1969" class="Bound">y</a> <a id="1971" class="Symbol">:</a> <a id="1973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1957" class="Bound">A</a><a id="1974" class="Symbol">}</a>
  <a id="1978" class="Symbol">→</a> <a id="1980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1967" class="Bound">x</a> <a id="1982" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="1984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1969" class="Bound">y</a>
    <a id="1990" class="Comment">-----</a>
  <a id="1998" class="Symbol">→</a> <a id="2000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1969" class="Bound">y</a> <a id="2002" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="2004" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1967" class="Bound">x</a>
<a id="2006" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1948" class="Function">sym</a> <a id="2010" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a> <a id="2015" class="Symbol">=</a> <a id="2017" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>{% endraw %}</pre>
How does this proof work? The argument to `sym` has type `x ≡ y`, but
on the left-hand side of the equation the argument has been
instantiated to the pattern `refl`, which requires that `x` and `y`
are the same.  Hence, for the right-hand side of the equation we need
a term of type `x ≡ x`, and `refl` will do.

It is instructive to develop `sym` interactively.  To start, we supply
a variable for the argument on the left, and a hole for the body on
the right:

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym e = {! !}

If we go into the hole and type `C-c C-,` then Agda reports:

    Goal: .y ≡ .x
    ————————————————————————————————————————————————————————————
    e  : .x ≡ .y
    .y : .A
    .x : .A
    .A : Set

If in the hole we type `C-c C-c e` then Agda will instantiate `e` to
all possible constructors, with one equation for each. There is only
one possible constructor:

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = {! !}

If we go into the hole again and type `C-c C-,` then Agda now reports:

     Goal: .x ≡ .x
     ————————————————————————————————————————————————————————————
     .x : .A
     .A : Set

This is the key step---Agda has worked out that `x` and `y` must be
the same to match the pattern `refl`!

Finally, if we go back into the hole and type `C-c C-r` it will
instantiate the hole with the one constructor that yields a value of
the expected type.

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = refl

This completes the definition as given above.

Transitivity is equally straightforward.
<pre class="Agda">{% raw %}<a id="trans"></a><a id="3692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3692" class="Function">trans</a> <a id="3698" class="Symbol">:</a> <a id="3700" class="Symbol">∀</a> <a id="3702" class="Symbol">{</a><a id="3703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3703" class="Bound">A</a> <a id="3705" class="Symbol">:</a> <a id="3707" class="PrimitiveType">Set</a><a id="3710" class="Symbol">}</a> <a id="3712" class="Symbol">{</a><a id="3713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3713" class="Bound">x</a> <a id="3715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3715" class="Bound">y</a> <a id="3717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3717" class="Bound">z</a> <a id="3719" class="Symbol">:</a> <a id="3721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3703" class="Bound">A</a><a id="3722" class="Symbol">}</a>
  <a id="3726" class="Symbol">→</a> <a id="3728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3713" class="Bound">x</a> <a id="3730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="3732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3715" class="Bound">y</a>
  <a id="3736" class="Symbol">→</a> <a id="3738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3715" class="Bound">y</a> <a id="3740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="3742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3717" class="Bound">z</a>
    <a id="3748" class="Comment">-----</a>
  <a id="3756" class="Symbol">→</a> <a id="3758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3713" class="Bound">x</a> <a id="3760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="3762" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3717" class="Bound">z</a>
<a id="3764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3692" class="Function">trans</a> <a id="3770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a> <a id="3775" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>  <a id="3781" class="Symbol">=</a>  <a id="3784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>{% endraw %}</pre>
Again, a useful exercise is to carry out an interactive development, checking
how Agda's knowledge changes as each of the two arguments is
instantiated.

## Congruence and substitution {#cong}

Equality satisfies _congruence_.  If two terms are equal,
they remain so after the same function is applied to both.
<pre class="Agda">{% raw %}<a id="cong"></a><a id="4124" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4124" class="Function">cong</a> <a id="4129" class="Symbol">:</a> <a id="4131" class="Symbol">∀</a> <a id="4133" class="Symbol">{</a><a id="4134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4134" class="Bound">A</a> <a id="4136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4136" class="Bound">B</a> <a id="4138" class="Symbol">:</a> <a id="4140" class="PrimitiveType">Set</a><a id="4143" class="Symbol">}</a> <a id="4145" class="Symbol">(</a><a id="4146" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4146" class="Bound">f</a> <a id="4148" class="Symbol">:</a> <a id="4150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4134" class="Bound">A</a> <a id="4152" class="Symbol">→</a> <a id="4154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4136" class="Bound">B</a><a id="4155" class="Symbol">)</a> <a id="4157" class="Symbol">{</a><a id="4158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4158" class="Bound">x</a> <a id="4160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4160" class="Bound">y</a> <a id="4162" class="Symbol">:</a> <a id="4164" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4134" class="Bound">A</a><a id="4165" class="Symbol">}</a>
  <a id="4169" class="Symbol">→</a> <a id="4171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4158" class="Bound">x</a> <a id="4173" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="4175" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4160" class="Bound">y</a>
    <a id="4181" class="Comment">---------</a>
  <a id="4193" class="Symbol">→</a> <a id="4195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4146" class="Bound">f</a> <a id="4197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4158" class="Bound">x</a> <a id="4199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="4201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4146" class="Bound">f</a> <a id="4203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4160" class="Bound">y</a>
<a id="4205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4124" class="Function">cong</a> <a id="4210" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4210" class="Bound">f</a> <a id="4212" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>  <a id="4218" class="Symbol">=</a>  <a id="4221" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>{% endraw %}</pre>

Congruence of functions with two arguments is similar.
<pre class="Agda">{% raw %}<a id="cong₂"></a><a id="4306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4306" class="Function">cong₂</a> <a id="4312" class="Symbol">:</a> <a id="4314" class="Symbol">∀</a> <a id="4316" class="Symbol">{</a><a id="4317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4317" class="Bound">A</a> <a id="4319" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4319" class="Bound">B</a> <a id="4321" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4321" class="Bound">C</a> <a id="4323" class="Symbol">:</a> <a id="4325" class="PrimitiveType">Set</a><a id="4328" class="Symbol">}</a> <a id="4330" class="Symbol">(</a><a id="4331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4331" class="Bound">f</a> <a id="4333" class="Symbol">:</a> <a id="4335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4317" class="Bound">A</a> <a id="4337" class="Symbol">→</a> <a id="4339" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4319" class="Bound">B</a> <a id="4341" class="Symbol">→</a> <a id="4343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4321" class="Bound">C</a><a id="4344" class="Symbol">)</a> <a id="4346" class="Symbol">{</a><a id="4347" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4347" class="Bound">u</a> <a id="4349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4349" class="Bound">x</a> <a id="4351" class="Symbol">:</a> <a id="4353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4317" class="Bound">A</a><a id="4354" class="Symbol">}</a> <a id="4356" class="Symbol">{</a><a id="4357" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4357" class="Bound">v</a> <a id="4359" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4359" class="Bound">y</a> <a id="4361" class="Symbol">:</a> <a id="4363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4319" class="Bound">B</a><a id="4364" class="Symbol">}</a>
  <a id="4368" class="Symbol">→</a> <a id="4370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4347" class="Bound">u</a> <a id="4372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="4374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4349" class="Bound">x</a>
  <a id="4378" class="Symbol">→</a> <a id="4380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4357" class="Bound">v</a> <a id="4382" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="4384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4359" class="Bound">y</a>
    <a id="4390" class="Comment">-------------</a>
  <a id="4406" class="Symbol">→</a> <a id="4408" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4331" class="Bound">f</a> <a id="4410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4347" class="Bound">u</a> <a id="4412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4357" class="Bound">v</a> <a id="4414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="4416" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4331" class="Bound">f</a> <a id="4418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4349" class="Bound">x</a> <a id="4420" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4359" class="Bound">y</a>
<a id="4422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4306" class="Function">cong₂</a> <a id="4428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4428" class="Bound">f</a> <a id="4430" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a> <a id="4435" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>  <a id="4441" class="Symbol">=</a>  <a id="4444" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>{% endraw %}</pre>

Equality is also a congruence in the function position of an application.
If two functions are equal, then applying them to the same term
yields equal terms.
<pre class="Agda">{% raw %}<a id="cong-app"></a><a id="4632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4632" class="Function">cong-app</a> <a id="4641" class="Symbol">:</a> <a id="4643" class="Symbol">∀</a> <a id="4645" class="Symbol">{</a><a id="4646" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4646" class="Bound">A</a> <a id="4648" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4648" class="Bound">B</a> <a id="4650" class="Symbol">:</a> <a id="4652" class="PrimitiveType">Set</a><a id="4655" class="Symbol">}</a> <a id="4657" class="Symbol">{</a><a id="4658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4658" class="Bound">f</a> <a id="4660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4660" class="Bound">g</a> <a id="4662" class="Symbol">:</a> <a id="4664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4646" class="Bound">A</a> <a id="4666" class="Symbol">→</a> <a id="4668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4648" class="Bound">B</a><a id="4669" class="Symbol">}</a>
  <a id="4673" class="Symbol">→</a> <a id="4675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4658" class="Bound">f</a> <a id="4677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="4679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4660" class="Bound">g</a>
    <a id="4685" class="Comment">---------------------</a>
  <a id="4709" class="Symbol">→</a> <a id="4711" class="Symbol">∀</a> <a id="4713" class="Symbol">(</a><a id="4714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4714" class="Bound">x</a> <a id="4716" class="Symbol">:</a> <a id="4718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4646" class="Bound">A</a><a id="4719" class="Symbol">)</a> <a id="4721" class="Symbol">→</a> <a id="4723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4658" class="Bound">f</a> <a id="4725" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4714" class="Bound">x</a> <a id="4727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="4729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4660" class="Bound">g</a> <a id="4731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4714" class="Bound">x</a>
<a id="4733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4632" class="Function">cong-app</a> <a id="4742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a> <a id="4747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4747" class="Bound">x</a> <a id="4749" class="Symbol">=</a> <a id="4751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>{% endraw %}</pre>

Equality also satisfies *substitution*.
If two values are equal and a predicate holds of the first then it also holds of the second.
<pre class="Agda">{% raw %}<a id="subst"></a><a id="4914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4914" class="Function">subst</a> <a id="4920" class="Symbol">:</a> <a id="4922" class="Symbol">∀</a> <a id="4924" class="Symbol">{</a><a id="4925" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4925" class="Bound">A</a> <a id="4927" class="Symbol">:</a> <a id="4929" class="PrimitiveType">Set</a><a id="4932" class="Symbol">}</a> <a id="4934" class="Symbol">{</a><a id="4935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4935" class="Bound">x</a> <a id="4937" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4937" class="Bound">y</a> <a id="4939" class="Symbol">:</a> <a id="4941" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4925" class="Bound">A</a><a id="4942" class="Symbol">}</a> <a id="4944" class="Symbol">(</a><a id="4945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4945" class="Bound">P</a> <a id="4947" class="Symbol">:</a> <a id="4949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4925" class="Bound">A</a> <a id="4951" class="Symbol">→</a> <a id="4953" class="PrimitiveType">Set</a><a id="4956" class="Symbol">)</a>
  <a id="4960" class="Symbol">→</a> <a id="4962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4935" class="Bound">x</a> <a id="4964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="4966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4937" class="Bound">y</a>
    <a id="4972" class="Comment">---------</a>
  <a id="4984" class="Symbol">→</a> <a id="4986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4945" class="Bound">P</a> <a id="4988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4935" class="Bound">x</a> <a id="4990" class="Symbol">→</a> <a id="4992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4945" class="Bound">P</a> <a id="4994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4937" class="Bound">y</a>
<a id="4996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4914" class="Function">subst</a> <a id="5002" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5002" class="Bound">P</a> <a id="5004" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a> <a id="5009" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5009" class="Bound">px</a> <a id="5012" class="Symbol">=</a> <a id="5014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5009" class="Bound">px</a>{% endraw %}</pre>


## Chains of equations

Here we show how to support reasoning with chains of equations
as used throughout the book.  We package the declarations
into a module, named `≡-Reasoning`, to match the format used in Agda's
standard library.
<pre class="Agda">{% raw %}<a id="5277" class="Keyword">module</a> <a id="≡-Reasoning"></a><a id="5284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5284" class="Module">≡-Reasoning</a> <a id="5296" class="Symbol">{</a><a id="5297" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5297" class="Bound">A</a> <a id="5299" class="Symbol">:</a> <a id="5301" class="PrimitiveType">Set</a><a id="5304" class="Symbol">}</a> <a id="5306" class="Keyword">where</a>

  <a id="5315" class="Keyword">infix</a>  <a id="5322" class="Number">1</a> <a id="5324" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5372" class="Function Operator">begin_</a>
  <a id="5333" class="Keyword">infixr</a> <a id="5340" class="Number">2</a> <a id="5342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5452" class="Function Operator">_≡⟨⟩_</a> <a id="5348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5537" class="Function Operator">_≡⟨_⟩_</a>
  <a id="5357" class="Keyword">infix</a>  <a id="5364" class="Number">3</a> <a id="5366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5652" class="Function Operator">_∎</a>

  <a id="≡-Reasoning.begin_"></a><a id="5372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5372" class="Function Operator">begin_</a> <a id="5379" class="Symbol">:</a> <a id="5381" class="Symbol">∀</a> <a id="5383" class="Symbol">{</a><a id="5384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5384" class="Bound">x</a> <a id="5386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5386" class="Bound">y</a> <a id="5388" class="Symbol">:</a> <a id="5390" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5297" class="Bound">A</a><a id="5391" class="Symbol">}</a>
    <a id="5397" class="Symbol">→</a> <a id="5399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5384" class="Bound">x</a> <a id="5401" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="5403" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5386" class="Bound">y</a>
      <a id="5411" class="Comment">-----</a>
    <a id="5421" class="Symbol">→</a> <a id="5423" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5384" class="Bound">x</a> <a id="5425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="5427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5386" class="Bound">y</a>
  <a id="5431" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5372" class="Function Operator">begin</a> <a id="5437" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5437" class="Bound">x≡y</a>  <a id="5442" class="Symbol">=</a>  <a id="5445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5437" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨⟩_"></a><a id="5452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5452" class="Function Operator">_≡⟨⟩_</a> <a id="5458" class="Symbol">:</a> <a id="5460" class="Symbol">∀</a> <a id="5462" class="Symbol">(</a><a id="5463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5463" class="Bound">x</a> <a id="5465" class="Symbol">:</a> <a id="5467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5297" class="Bound">A</a><a id="5468" class="Symbol">)</a> <a id="5470" class="Symbol">{</a><a id="5471" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5471" class="Bound">y</a> <a id="5473" class="Symbol">:</a> <a id="5475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5297" class="Bound">A</a><a id="5476" class="Symbol">}</a>
    <a id="5482" class="Symbol">→</a> <a id="5484" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5463" class="Bound">x</a> <a id="5486" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="5488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5471" class="Bound">y</a>
      <a id="5496" class="Comment">-----</a>
    <a id="5506" class="Symbol">→</a> <a id="5508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5463" class="Bound">x</a> <a id="5510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="5512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5471" class="Bound">y</a>
  <a id="5516" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5516" class="Bound">x</a> <a id="5518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5452" class="Function Operator">≡⟨⟩</a> <a id="5522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5522" class="Bound">x≡y</a>  <a id="5527" class="Symbol">=</a>  <a id="5530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5522" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨_⟩_"></a><a id="5537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5537" class="Function Operator">_≡⟨_⟩_</a> <a id="5544" class="Symbol">:</a> <a id="5546" class="Symbol">∀</a> <a id="5548" class="Symbol">(</a><a id="5549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5549" class="Bound">x</a> <a id="5551" class="Symbol">:</a> <a id="5553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5297" class="Bound">A</a><a id="5554" class="Symbol">)</a> <a id="5556" class="Symbol">{</a><a id="5557" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5557" class="Bound">y</a> <a id="5559" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5559" class="Bound">z</a> <a id="5561" class="Symbol">:</a> <a id="5563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5297" class="Bound">A</a><a id="5564" class="Symbol">}</a>
    <a id="5570" class="Symbol">→</a> <a id="5572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5549" class="Bound">x</a> <a id="5574" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="5576" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5557" class="Bound">y</a>
    <a id="5582" class="Symbol">→</a> <a id="5584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5557" class="Bound">y</a> <a id="5586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="5588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5559" class="Bound">z</a>
      <a id="5596" class="Comment">-----</a>
    <a id="5606" class="Symbol">→</a> <a id="5608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5549" class="Bound">x</a> <a id="5610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="5612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5559" class="Bound">z</a>
  <a id="5616" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5616" class="Bound">x</a> <a id="5618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5537" class="Function Operator">≡⟨</a> <a id="5621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5621" class="Bound">x≡y</a> <a id="5625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5537" class="Function Operator">⟩</a> <a id="5627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5627" class="Bound">y≡z</a>  <a id="5632" class="Symbol">=</a>  <a id="5635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3692" class="Function">trans</a> <a id="5641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5621" class="Bound">x≡y</a> <a id="5645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5627" class="Bound">y≡z</a>

  <a id="≡-Reasoning._∎"></a><a id="5652" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5652" class="Function Operator">_∎</a> <a id="5655" class="Symbol">:</a> <a id="5657" class="Symbol">∀</a> <a id="5659" class="Symbol">(</a><a id="5660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5660" class="Bound">x</a> <a id="5662" class="Symbol">:</a> <a id="5664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5297" class="Bound">A</a><a id="5665" class="Symbol">)</a>
      <a id="5673" class="Comment">-----</a>
    <a id="5683" class="Symbol">→</a> <a id="5685" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5660" class="Bound">x</a> <a id="5687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="5689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5660" class="Bound">x</a>
  <a id="5693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5693" class="Bound">x</a> <a id="5695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5652" class="Function Operator">∎</a>  <a id="5698" class="Symbol">=</a>  <a id="5701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>

<a id="5707" class="Keyword">open</a> <a id="5712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5284" class="Module">≡-Reasoning</a>{% endraw %}</pre>
This is our first use of a nested module. It consists of the keyword
`module` followed by the module name and any parameters, explicit or
implicit, the keyword `where`, and the contents of the module indented.
Modules may contain any sort of declaration, including nested modules.
Nested modules are similar to the top-level modules that constitute
each chapter of this book, save that the body of a top-level module
need not be indented.  Opening the module makes all of the definitions
available in the current environment.

As an example, let's look at a proof of transitivity
as a chain of equations.
<pre class="Agda">{% raw %}<a id="trans′"></a><a id="6353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6353" class="Function">trans′</a> <a id="6360" class="Symbol">:</a> <a id="6362" class="Symbol">∀</a> <a id="6364" class="Symbol">{</a><a id="6365" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6365" class="Bound">A</a> <a id="6367" class="Symbol">:</a> <a id="6369" class="PrimitiveType">Set</a><a id="6372" class="Symbol">}</a> <a id="6374" class="Symbol">{</a><a id="6375" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6375" class="Bound">x</a> <a id="6377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6377" class="Bound">y</a> <a id="6379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6379" class="Bound">z</a> <a id="6381" class="Symbol">:</a> <a id="6383" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6365" class="Bound">A</a><a id="6384" class="Symbol">}</a>
  <a id="6388" class="Symbol">→</a> <a id="6390" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6375" class="Bound">x</a> <a id="6392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="6394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6377" class="Bound">y</a>
  <a id="6398" class="Symbol">→</a> <a id="6400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6377" class="Bound">y</a> <a id="6402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="6404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6379" class="Bound">z</a>
    <a id="6410" class="Comment">-----</a>
  <a id="6418" class="Symbol">→</a> <a id="6420" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6375" class="Bound">x</a> <a id="6422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="6424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6379" class="Bound">z</a>
<a id="6426" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6353" class="Function">trans′</a> <a id="6433" class="Symbol">{</a><a id="6434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6434" class="Bound">A</a><a id="6435" class="Symbol">}</a> <a id="6437" class="Symbol">{</a><a id="6438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6438" class="Bound">x</a><a id="6439" class="Symbol">}</a> <a id="6441" class="Symbol">{</a><a id="6442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6442" class="Bound">y</a><a id="6443" class="Symbol">}</a> <a id="6445" class="Symbol">{</a><a id="6446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6446" class="Bound">z</a><a id="6447" class="Symbol">}</a> <a id="6449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6449" class="Bound">x≡y</a> <a id="6453" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6453" class="Bound">y≡z</a> <a id="6457" class="Symbol">=</a>
  <a id="6461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5372" class="Function Operator">begin</a>
    <a id="6471" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6438" class="Bound">x</a>
  <a id="6475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5537" class="Function Operator">≡⟨</a> <a id="6478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6449" class="Bound">x≡y</a> <a id="6482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5537" class="Function Operator">⟩</a>
    <a id="6488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6442" class="Bound">y</a>
  <a id="6492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5537" class="Function Operator">≡⟨</a> <a id="6495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6453" class="Bound">y≡z</a> <a id="6499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5537" class="Function Operator">⟩</a>
    <a id="6505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6446" class="Bound">z</a>
  <a id="6509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5652" class="Function Operator">∎</a>{% endraw %}</pre>
According to the fixity declarations, the body parses as follows:

    begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))

The application of `begin` is purely cosmetic, as it simply returns
its argument.  That argument consists of `_≡⟨_⟩_` applied to `x`,
`x≡y`, and `y ≡⟨ y≡z ⟩ (z ∎)`.  The first argument is a term, `x`,
while the second and third arguments are both proofs of equations, in
particular proofs of `x ≡ y` and `y ≡ z` respectively, which are
combined by `trans` in the body of `_≡⟨_⟩_` to yield a proof of `x ≡
z`.  The proof of `y ≡ z` consists of `_≡⟨_⟩_` applied to `y`, `y≡z`,
and `z ∎`.  The first argument is a term, `y`, while the second and
third arguments are both proofs of equations, in particular proofs of
`y ≡ z` and `z ≡ z` respectively, which are combined by `trans` in the
body of `_≡⟨_⟩_` to yield a proof of `y ≡ z`.  Finally, the proof of
`z ≡ z` consists of `_∎` applied to the term `z`, which yields `refl`.
After simplification, the body is equivalent to the term:

    trans x≡y (trans y≡z refl)

We could replace any use of a chain of equations by a chain of
applications of `trans`; the result would be more compact but harder
to read.  The trick behind `∎` means that a chain of equalities
simplifies to a chain of applications of `trans` than ends in `trans e
refl`, where `e` is a term that proves some equality, even though `e`
alone would do.


## Chains of equations, another example

As a second example of chains of equations, we repeat the proof that addition
is commutative.  We first repeat the definitions of naturals and addition.
We cannot import them because (as noted at the beginning of this chapter)
it would cause a conflict.
<pre class="Agda">{% raw %}<a id="8210" class="Keyword">data</a> <a id="ℕ"></a><a id="8215" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8215" class="Datatype">ℕ</a> <a id="8217" class="Symbol">:</a> <a id="8219" class="PrimitiveType">Set</a> <a id="8223" class="Keyword">where</a>
  <a id="ℕ.zero"></a><a id="8231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8231" class="InductiveConstructor">zero</a> <a id="8236" class="Symbol">:</a> <a id="8238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8215" class="Datatype">ℕ</a>
  <a id="ℕ.suc"></a><a id="8242" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8242" class="InductiveConstructor">suc</a>  <a id="8247" class="Symbol">:</a> <a id="8249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8215" class="Datatype">ℕ</a> <a id="8251" class="Symbol">→</a> <a id="8253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8215" class="Datatype">ℕ</a>

<a id="_+_"></a><a id="8256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">_+_</a> <a id="8260" class="Symbol">:</a> <a id="8262" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8215" class="Datatype">ℕ</a> <a id="8264" class="Symbol">→</a> <a id="8266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8215" class="Datatype">ℕ</a> <a id="8268" class="Symbol">→</a> <a id="8270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8215" class="Datatype">ℕ</a>
<a id="8272" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8231" class="InductiveConstructor">zero</a>    <a id="8280" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="8282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8282" class="Bound">n</a>  <a id="8285" class="Symbol">=</a>  <a id="8288" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8282" class="Bound">n</a>
<a id="8290" class="Symbol">(</a><a id="8291" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8242" class="InductiveConstructor">suc</a> <a id="8295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8295" class="Bound">m</a><a id="8296" class="Symbol">)</a> <a id="8298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="8300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8300" class="Bound">n</a>  <a id="8303" class="Symbol">=</a>  <a id="8306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8242" class="InductiveConstructor">suc</a> <a id="8310" class="Symbol">(</a><a id="8311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8295" class="Bound">m</a> <a id="8313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="8315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8300" class="Bound">n</a><a id="8316" class="Symbol">)</a>{% endraw %}</pre>

To save space we postulate (rather than prove in full) two lemmas.
<pre class="Agda">{% raw %}<a id="8410" class="Keyword">postulate</a>
  <a id="+-identity"></a><a id="8422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8422" class="Postulate">+-identity</a> <a id="8433" class="Symbol">:</a> <a id="8435" class="Symbol">∀</a> <a id="8437" class="Symbol">(</a><a id="8438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8438" class="Bound">m</a> <a id="8440" class="Symbol">:</a> <a id="8442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8215" class="Datatype">ℕ</a><a id="8443" class="Symbol">)</a> <a id="8445" class="Symbol">→</a> <a id="8447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8438" class="Bound">m</a> <a id="8449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="8451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8231" class="InductiveConstructor">zero</a> <a id="8456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="8458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8438" class="Bound">m</a>
  <a id="+-suc"></a><a id="8462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8462" class="Postulate">+-suc</a> <a id="8468" class="Symbol">:</a> <a id="8470" class="Symbol">∀</a> <a id="8472" class="Symbol">(</a><a id="8473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8473" class="Bound">m</a> <a id="8475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8475" class="Bound">n</a> <a id="8477" class="Symbol">:</a> <a id="8479" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8215" class="Datatype">ℕ</a><a id="8480" class="Symbol">)</a> <a id="8482" class="Symbol">→</a> <a id="8484" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8473" class="Bound">m</a> <a id="8486" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="8488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8242" class="InductiveConstructor">suc</a> <a id="8492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8475" class="Bound">n</a> <a id="8494" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="8496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8242" class="InductiveConstructor">suc</a> <a id="8500" class="Symbol">(</a><a id="8501" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8473" class="Bound">m</a> <a id="8503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="8505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8475" class="Bound">n</a><a id="8506" class="Symbol">)</a>{% endraw %}</pre>
This is our first use of a _postulate_.  A postulate specifies a
signature for an identifier but no definition.  Here we postulate
something proved earlier to save space.  Postulates must be used with
caution.  If we postulate something false then we could use Agda to
prove anything whatsoever.

We then repeat the proof of commutativity.
<pre class="Agda">{% raw %}<a id="+-comm"></a><a id="8872" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8872" class="Function">+-comm</a> <a id="8879" class="Symbol">:</a> <a id="8881" class="Symbol">∀</a> <a id="8883" class="Symbol">(</a><a id="8884" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8884" class="Bound">m</a> <a id="8886" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8886" class="Bound">n</a> <a id="8888" class="Symbol">:</a> <a id="8890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8215" class="Datatype">ℕ</a><a id="8891" class="Symbol">)</a> <a id="8893" class="Symbol">→</a> <a id="8895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8884" class="Bound">m</a> <a id="8897" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="8899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8886" class="Bound">n</a> <a id="8901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="8903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8886" class="Bound">n</a> <a id="8905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="8907" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8884" class="Bound">m</a>
<a id="8909" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8872" class="Function">+-comm</a> <a id="8916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8916" class="Bound">m</a> <a id="8918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8231" class="InductiveConstructor">zero</a> <a id="8923" class="Symbol">=</a>
  <a id="8927" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5372" class="Function Operator">begin</a>
    <a id="8937" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8916" class="Bound">m</a> <a id="8939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="8941" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8231" class="InductiveConstructor">zero</a>
  <a id="8948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5537" class="Function Operator">≡⟨</a> <a id="8951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8422" class="Postulate">+-identity</a> <a id="8962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8916" class="Bound">m</a> <a id="8964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5537" class="Function Operator">⟩</a>
    <a id="8970" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8916" class="Bound">m</a>
  <a id="8974" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5452" class="Function Operator">≡⟨⟩</a>
    <a id="8982" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8231" class="InductiveConstructor">zero</a> <a id="8987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="8989" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8916" class="Bound">m</a>
  <a id="8993" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5652" class="Function Operator">∎</a>
<a id="8995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8872" class="Function">+-comm</a> <a id="9002" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9002" class="Bound">m</a> <a id="9004" class="Symbol">(</a><a id="9005" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8242" class="InductiveConstructor">suc</a> <a id="9009" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9009" class="Bound">n</a><a id="9010" class="Symbol">)</a> <a id="9012" class="Symbol">=</a>
  <a id="9016" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5372" class="Function Operator">begin</a>
    <a id="9026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9002" class="Bound">m</a> <a id="9028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="9030" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8242" class="InductiveConstructor">suc</a> <a id="9034" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9009" class="Bound">n</a>
  <a id="9038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5537" class="Function Operator">≡⟨</a> <a id="9041" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8462" class="Postulate">+-suc</a> <a id="9047" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9002" class="Bound">m</a> <a id="9049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9009" class="Bound">n</a> <a id="9051" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5537" class="Function Operator">⟩</a>
    <a id="9057" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8242" class="InductiveConstructor">suc</a> <a id="9061" class="Symbol">(</a><a id="9062" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9002" class="Bound">m</a> <a id="9064" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="9066" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9009" class="Bound">n</a><a id="9067" class="Symbol">)</a>
  <a id="9071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5537" class="Function Operator">≡⟨</a> <a id="9074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4124" class="Function">cong</a> <a id="9079" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8242" class="InductiveConstructor">suc</a> <a id="9083" class="Symbol">(</a><a id="9084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8872" class="Function">+-comm</a> <a id="9091" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9002" class="Bound">m</a> <a id="9093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9009" class="Bound">n</a><a id="9094" class="Symbol">)</a> <a id="9096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5537" class="Function Operator">⟩</a>
    <a id="9102" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8242" class="InductiveConstructor">suc</a> <a id="9106" class="Symbol">(</a><a id="9107" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9009" class="Bound">n</a> <a id="9109" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="9111" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9002" class="Bound">m</a><a id="9112" class="Symbol">)</a>
  <a id="9116" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5452" class="Function Operator">≡⟨⟩</a>
    <a id="9124" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8242" class="InductiveConstructor">suc</a> <a id="9128" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9009" class="Bound">n</a> <a id="9130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="9132" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9002" class="Bound">m</a>
  <a id="9136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5652" class="Function Operator">∎</a>{% endraw %}</pre>
The reasoning here is similar to that in the
preceding section, the one addition being the use of
`_≡⟨⟩_`, which we use when no justification is required.
One can think of occurrences of `≡⟨⟩` as an equivalent
to `≡⟨ refl ⟩`.

Agda always treats a term as equivalent to its
simplified term.  The reason that one can write

      suc (n + m)
    ≡⟨⟩
      suc n + m

is because Agda treats both terms as the same.
This also means that one could instead interchange
the lines and write

      suc n + m
    ≡⟨⟩
      suc (n + m)

and Agda would not object. Agda only checks that the terms separated
by `≡⟨⟩` have the same simplified form; it's up to us to write them in
an order that will make sense to the reader.


#### Exercise `≤-reasoning` (stretch)

The proof of monotonicity from
Chapter [Relations]({{ site.baseurl }}{% link out/plfa/Relations.md%})
can be written in a more readable form by using an anologue of our
notation for `≡-reasoning`.  Define `≤-reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite both `+-monoˡ-≤` and `+-mono-≤`.



## Rewriting

Consider a property of natural numbers, such as being even.
We repeat the earlier definition.
<pre class="Agda">{% raw %}<a id="10365" class="Keyword">data</a> <a id="even"></a><a id="10370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10370" class="Datatype">even</a> <a id="10375" class="Symbol">:</a> <a id="10377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8215" class="Datatype">ℕ</a> <a id="10379" class="Symbol">→</a> <a id="10381" class="PrimitiveType">Set</a>
<a id="10385" class="Keyword">data</a> <a id="odd"></a><a id="10390" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10390" class="Datatype">odd</a>  <a id="10395" class="Symbol">:</a> <a id="10397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8215" class="Datatype">ℕ</a> <a id="10399" class="Symbol">→</a> <a id="10401" class="PrimitiveType">Set</a>

<a id="10406" class="Keyword">data</a> <a id="10411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10370" class="Datatype">even</a> <a id="10416" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="10425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10425" class="InductiveConstructor">even-zero</a> <a id="10435" class="Symbol">:</a> <a id="10437" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10370" class="Datatype">even</a> <a id="10442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8231" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="10450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10450" class="InductiveConstructor">even-suc</a> <a id="10459" class="Symbol">:</a> <a id="10461" class="Symbol">∀</a> <a id="10463" class="Symbol">{</a><a id="10464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10464" class="Bound">n</a> <a id="10466" class="Symbol">:</a> <a id="10468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8215" class="Datatype">ℕ</a><a id="10469" class="Symbol">}</a>
    <a id="10475" class="Symbol">→</a> <a id="10477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10390" class="Datatype">odd</a> <a id="10481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10464" class="Bound">n</a>
      <a id="10489" class="Comment">------------</a>
    <a id="10506" class="Symbol">→</a> <a id="10508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10370" class="Datatype">even</a> <a id="10513" class="Symbol">(</a><a id="10514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8242" class="InductiveConstructor">suc</a> <a id="10518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10464" class="Bound">n</a><a id="10519" class="Symbol">)</a>

<a id="10522" class="Keyword">data</a> <a id="10527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10390" class="Datatype">odd</a> <a id="10531" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="10539" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10539" class="InductiveConstructor">odd-suc</a> <a id="10547" class="Symbol">:</a> <a id="10549" class="Symbol">∀</a> <a id="10551" class="Symbol">{</a><a id="10552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10552" class="Bound">n</a> <a id="10554" class="Symbol">:</a> <a id="10556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8215" class="Datatype">ℕ</a><a id="10557" class="Symbol">}</a>
    <a id="10563" class="Symbol">→</a> <a id="10565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10370" class="Datatype">even</a> <a id="10570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10552" class="Bound">n</a>
      <a id="10578" class="Comment">-----------</a>
    <a id="10594" class="Symbol">→</a> <a id="10596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10390" class="Datatype">odd</a> <a id="10600" class="Symbol">(</a><a id="10601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8242" class="InductiveConstructor">suc</a> <a id="10605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10552" class="Bound">n</a><a id="10606" class="Symbol">)</a>{% endraw %}</pre>
In the previous section, we proved addition is commutative.  Given
evidence that `even (m + n)` holds, we ought also to be able to take
that as evidence that `even (n + m)` holds.

Agda includes special notation to support just this kind of reasoning.
To enable this notation, we use pragmas to tell Agda which type
corresponds to equivalence.
<pre class="Agda">{% raw %}<a id="10976" class="Symbol">{-#</a> <a id="10980" class="Keyword">BUILTIN</a> EQUALITY <a id="10997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">_≡_</a> <a id="11001" class="Symbol">#-}</a>{% endraw %}</pre>

We can then prove the desired property as follows.
<pre class="Agda">{% raw %}<a id="even-comm"></a><a id="11081" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11081" class="Function">even-comm</a> <a id="11091" class="Symbol">:</a> <a id="11093" class="Symbol">∀</a> <a id="11095" class="Symbol">(</a><a id="11096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11096" class="Bound">m</a> <a id="11098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11098" class="Bound">n</a> <a id="11100" class="Symbol">:</a> <a id="11102" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8215" class="Datatype">ℕ</a><a id="11103" class="Symbol">)</a>
  <a id="11107" class="Symbol">→</a> <a id="11109" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10370" class="Datatype">even</a> <a id="11114" class="Symbol">(</a><a id="11115" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11096" class="Bound">m</a> <a id="11117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="11119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11098" class="Bound">n</a><a id="11120" class="Symbol">)</a>
    <a id="11126" class="Comment">------------</a>
  <a id="11141" class="Symbol">→</a> <a id="11143" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10370" class="Datatype">even</a> <a id="11148" class="Symbol">(</a><a id="11149" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11098" class="Bound">n</a> <a id="11151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="11153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11096" class="Bound">m</a><a id="11154" class="Symbol">)</a>
<a id="11156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11081" class="Function">even-comm</a> <a id="11166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11166" class="Bound">m</a> <a id="11168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11168" class="Bound">n</a> <a id="11170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11170" class="Bound">ev</a>  <a id="11174" class="Keyword">rewrite</a> <a id="11182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8872" class="Function">+-comm</a> <a id="11189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11168" class="Bound">n</a> <a id="11191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11166" class="Bound">m</a>  <a id="11194" class="Symbol">=</a>  <a id="11197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11170" class="Bound">ev</a>{% endraw %}</pre>
Here `ev` ranges over evidence that `even (m + n)` holds, and we show
that it is also provides evidence that `even (n + m)` holds.  In
general, the keyword `rewrite` is followed by evidence of an
equivalence, and that equivalence is used to rewrite the type of the
goal and of any variable in scope.

It is instructive to develop `even-comm` interactively.  To start, we
supply variables for the arguments on the left, and a hole for the
body on the right:

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev = {! !}

If we go into the hole and type `C-c C-,` then Agda reports:

    Goal: even (n + m)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

Now we add the rewrite.

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev rewrite +-comm m n = {! !}

If we go into the hole again and type `C-c C-,` then Agda now reports:

    Goal: even (n + m)
    ————————————————————————————————————————————————————————————
    ev : even (n + m)
    n  : ℕ
    m  : ℕ

The arguments have been swapped in the goal.  Now it is trivial to see
that `ev` satisfies the goal, and typing `C-c C-a` in the hole causes
it to be filled with `ev`.


## Multiple rewrites

One may perform multiple rewrites, each separated by a vertical bar.  For instance,
here is a second proof that addition is commutative, relying on rewrites rather
than chains of equalities.
<pre class="Agda">{% raw %}<a id="+-comm′"></a><a id="12751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12751" class="Function">+-comm′</a> <a id="12759" class="Symbol">:</a> <a id="12761" class="Symbol">∀</a> <a id="12763" class="Symbol">(</a><a id="12764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12764" class="Bound">m</a> <a id="12766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12766" class="Bound">n</a> <a id="12768" class="Symbol">:</a> <a id="12770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8215" class="Datatype">ℕ</a><a id="12771" class="Symbol">)</a> <a id="12773" class="Symbol">→</a> <a id="12775" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12764" class="Bound">m</a> <a id="12777" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="12779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12766" class="Bound">n</a> <a id="12781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="12783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12766" class="Bound">n</a> <a id="12785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="12787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12764" class="Bound">m</a>
<a id="12789" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12751" class="Function">+-comm′</a> <a id="12797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8231" class="InductiveConstructor">zero</a>    <a id="12805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12805" class="Bound">n</a>  <a id="12808" class="Keyword">rewrite</a> <a id="12816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8422" class="Postulate">+-identity</a> <a id="12827" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12805" class="Bound">n</a>            <a id="12840" class="Symbol">=</a>  <a id="12843" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>
<a id="12848" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12751" class="Function">+-comm′</a> <a id="12856" class="Symbol">(</a><a id="12857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8242" class="InductiveConstructor">suc</a> <a id="12861" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12861" class="Bound">m</a><a id="12862" class="Symbol">)</a> <a id="12864" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12864" class="Bound">n</a>  <a id="12867" class="Keyword">rewrite</a> <a id="12875" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8462" class="Postulate">+-suc</a> <a id="12881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12864" class="Bound">n</a> <a id="12883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12861" class="Bound">m</a> <a id="12885" class="Symbol">|</a> <a id="12887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8872" class="Function">+-comm</a> <a id="12894" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12861" class="Bound">m</a> <a id="12896" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12864" class="Bound">n</a>  <a id="12899" class="Symbol">=</a>  <a id="12902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>{% endraw %}</pre>
This is far more compact.  Among other things, whereas the previous
proof required `cong suc (+-comm m n)` as the justification to invoke
the inductive hypothesis, here it is sufficient to rewrite with
`+-comm m n`, as rewriting automatically takes congruence into
account.  Although proofs with rewriting are shorter, proofs as chains
of equalities are easier to follow, and we will stick with the latter
when feasible.


## Rewriting expanded

The `rewrite` notation is in fact shorthand for an appropriate use of `with`
abstraction.
<pre class="Agda">{% raw %}<a id="even-comm′"></a><a id="13467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13467" class="Function">even-comm′</a> <a id="13478" class="Symbol">:</a> <a id="13480" class="Symbol">∀</a> <a id="13482" class="Symbol">(</a><a id="13483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13483" class="Bound">m</a> <a id="13485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13485" class="Bound">n</a> <a id="13487" class="Symbol">:</a> <a id="13489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8215" class="Datatype">ℕ</a><a id="13490" class="Symbol">)</a>
  <a id="13494" class="Symbol">→</a> <a id="13496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10370" class="Datatype">even</a> <a id="13501" class="Symbol">(</a><a id="13502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13483" class="Bound">m</a> <a id="13504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="13506" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13485" class="Bound">n</a><a id="13507" class="Symbol">)</a>
    <a id="13513" class="Comment">------------</a>
  <a id="13528" class="Symbol">→</a> <a id="13530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10370" class="Datatype">even</a> <a id="13535" class="Symbol">(</a><a id="13536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13485" class="Bound">n</a> <a id="13538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="13540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13483" class="Bound">m</a><a id="13541" class="Symbol">)</a>
<a id="13543" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13467" class="Function">even-comm′</a> <a id="13554" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13554" class="Bound">m</a> <a id="13556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13556" class="Bound">n</a> <a id="13558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13558" class="Bound">ev</a> <a id="13561" class="Keyword">with</a>     <a id="13570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13554" class="Bound">m</a> <a id="13572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="13574" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13556" class="Bound">n</a>  <a id="13577" class="Symbol">|</a> <a id="13579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8872" class="Function">+-comm</a> <a id="13586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13554" class="Bound">m</a> <a id="13588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13556" class="Bound">n</a> 
<a id="13591" class="Symbol">...</a>                  <a id="13612" class="Symbol">|</a>   <a id="13616" class="DottedPattern Symbol">.(</a><a id="13618" class="DottedPattern Bound">n</a> <a id="13620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="DottedPattern Function Operator">+</a> <a id="13622" class="DottedPattern Bound">m</a><a id="13623" class="DottedPattern Symbol">)</a> <a id="13625" class="Symbol">|</a> <a id="13627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>         <a id="13640" class="Symbol">=</a> <a id="13642" class="Bound">ev</a>{% endraw %}</pre>
The first clause asserts that `m + n` and `n + m` are identical, and
the second clause justifies that assertion with evidence of the
appropriate equivalence.  Note the use of the _dot pattern_, `.(n +
m)`.  A dot pattern consists of a dot followed by an expression, and
is used when other information forces the value matched to be equal to
the value of the expression in the dot pattern.  In this case, the
identification of `m + n` and `n + m` is justified by the subsequent
matching of `+-comm m n` against `refl`.  One might think that the
first clause is redundant as the information is inherent in the second
clause, but in fact Agda is rather picky on this point: omitting the
first clause or reversing the order of the clauses will cause Agda to
report an error.  (Try it and see!)

In this case, we can avoid rewrite by simply applying substitution.
<pre class="Agda">{% raw %}<a id="even-comm″"></a><a id="14528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14528" class="Function">even-comm″</a> <a id="14539" class="Symbol">:</a> <a id="14541" class="Symbol">∀</a> <a id="14543" class="Symbol">(</a><a id="14544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14544" class="Bound">m</a> <a id="14546" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14546" class="Bound">n</a> <a id="14548" class="Symbol">:</a> <a id="14550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8215" class="Datatype">ℕ</a><a id="14551" class="Symbol">)</a>
  <a id="14555" class="Symbol">→</a> <a id="14557" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10370" class="Datatype">even</a> <a id="14562" class="Symbol">(</a><a id="14563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14544" class="Bound">m</a> <a id="14565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="14567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14546" class="Bound">n</a><a id="14568" class="Symbol">)</a>
    <a id="14574" class="Comment">------------</a>
  <a id="14589" class="Symbol">→</a> <a id="14591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10370" class="Datatype">even</a> <a id="14596" class="Symbol">(</a><a id="14597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14546" class="Bound">n</a> <a id="14599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8256" class="Function Operator">+</a> <a id="14601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14544" class="Bound">m</a><a id="14602" class="Symbol">)</a>
<a id="14604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14528" class="Function">even-comm″</a> <a id="14615" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14615" class="Bound">m</a> <a id="14617" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14617" class="Bound">n</a>  <a id="14620" class="Symbol">=</a>  <a id="14623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4914" class="Function">subst</a> <a id="14629" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10370" class="Datatype">even</a> <a id="14634" class="Symbol">(</a><a id="14635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8872" class="Function">+-comm</a> <a id="14642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14615" class="Bound">m</a> <a id="14644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14617" class="Bound">n</a><a id="14645" class="Symbol">)</a>{% endraw %}</pre>
Nonetheless, rewrite is a vital part of the Agda toolkit,
as earlier examples have shown.


## Leibniz equality

The form of asserting equivalence that we have used is due to Martin
Löf, and was published in 1975.  An older form is due to Leibniz, and
was published in 1686.  Leibniz asserted the _identity of
indiscernibles_: two objects are equal if and only if they satisfy the
same properties. This principle sometimes goes by the name Leibniz'
Law, and is closely related to Spock's Law, "A difference that makes
no difference is no difference".  Here we define Leibniz equality,
and show that two terms satisfy Leibniz equality if and only if they
satisfy Martin Löf equivalence.

Leibniz equality is usually formalised to state that `x ≐ y`
holds if every property `P` that holds of `x` also holds of
`y`.  Perhaps surprisingly, this definition is
sufficient to also ensure the converse, that every property `P` that
holds of `y` also holds of `x`.

Let `x` and `y` be objects of type `A`. We say that `x ≐ y` holds if
for every predicate `P` over type `A` we have that `P x` implies `P y`.
<pre class="Agda">{% raw %}<a id="_≐_"></a><a id="15769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15769" class="Function Operator">_≐_</a> <a id="15773" class="Symbol">:</a> <a id="15775" class="Symbol">∀</a> <a id="15777" class="Symbol">{</a><a id="15778" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15778" class="Bound">A</a> <a id="15780" class="Symbol">:</a> <a id="15782" class="PrimitiveType">Set</a><a id="15785" class="Symbol">}</a> <a id="15787" class="Symbol">(</a><a id="15788" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15788" class="Bound">x</a> <a id="15790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15790" class="Bound">y</a> <a id="15792" class="Symbol">:</a> <a id="15794" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15778" class="Bound">A</a><a id="15795" class="Symbol">)</a> <a id="15797" class="Symbol">→</a> <a id="15799" class="PrimitiveType">Set₁</a>
<a id="15804" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15769" class="Function Operator">_≐_</a> <a id="15808" class="Symbol">{</a><a id="15809" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15809" class="Bound">A</a><a id="15810" class="Symbol">}</a> <a id="15812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15812" class="Bound">x</a> <a id="15814" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15814" class="Bound">y</a> <a id="15816" class="Symbol">=</a> <a id="15818" class="Symbol">∀</a> <a id="15820" class="Symbol">(</a><a id="15821" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15821" class="Bound">P</a> <a id="15823" class="Symbol">:</a> <a id="15825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15809" class="Bound">A</a> <a id="15827" class="Symbol">→</a> <a id="15829" class="PrimitiveType">Set</a><a id="15832" class="Symbol">)</a> <a id="15834" class="Symbol">→</a> <a id="15836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15821" class="Bound">P</a> <a id="15838" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15812" class="Bound">x</a> <a id="15840" class="Symbol">→</a> <a id="15842" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15821" class="Bound">P</a> <a id="15844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15814" class="Bound">y</a>{% endraw %}</pre>
We cannot write the left-hand side of the equation as `x ≐ y`,
and instead we write `_≐_ {A} x y` to provide access to the implicit
parameter `A` which appears on the right-hand side.

This is our first use of _levels_.  We cannot assign `Set` the type
`Set`, since this would lead to contradictions such as Russel's
Paradox and Girard's Paradox.  Instead, there is a hierarchy of types,
where `Set : Set₁`, `Set₁ : Set₂`, and so on.  In fact, `Set` itself
is just an abbreviation for `Set₀`.  Since the equation defining `_≐_`
mentions `Set` on the right-hand side, the corresponding signature
must use `Set₁`.  We say a bit more about levels below.

Leibniz equality is reflexive and transitive,
where the first follows by a variant of the identity function
and the second by a variant of function composition.
<pre class="Agda">{% raw %}<a id="refl-≐"></a><a id="16683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16683" class="Function">refl-≐</a> <a id="16690" class="Symbol">:</a> <a id="16692" class="Symbol">∀</a> <a id="16694" class="Symbol">{</a><a id="16695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16695" class="Bound">A</a> <a id="16697" class="Symbol">:</a> <a id="16699" class="PrimitiveType">Set</a><a id="16702" class="Symbol">}</a> <a id="16704" class="Symbol">{</a><a id="16705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16705" class="Bound">x</a> <a id="16707" class="Symbol">:</a> <a id="16709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16695" class="Bound">A</a><a id="16710" class="Symbol">}</a>
  <a id="16714" class="Symbol">→</a> <a id="16716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16705" class="Bound">x</a> <a id="16718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15769" class="Function Operator">≐</a> <a id="16720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16705" class="Bound">x</a>
<a id="16722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16683" class="Function">refl-≐</a> <a id="16729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16729" class="Bound">P</a> <a id="16731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16731" class="Bound">Px</a>  <a id="16735" class="Symbol">=</a>  <a id="16738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16731" class="Bound">Px</a>

<a id="trans-≐"></a><a id="16742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16742" class="Function">trans-≐</a> <a id="16750" class="Symbol">:</a> <a id="16752" class="Symbol">∀</a> <a id="16754" class="Symbol">{</a><a id="16755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16755" class="Bound">A</a> <a id="16757" class="Symbol">:</a> <a id="16759" class="PrimitiveType">Set</a><a id="16762" class="Symbol">}</a> <a id="16764" class="Symbol">{</a><a id="16765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16765" class="Bound">x</a> <a id="16767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16767" class="Bound">y</a> <a id="16769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16769" class="Bound">z</a> <a id="16771" class="Symbol">:</a> <a id="16773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16755" class="Bound">A</a><a id="16774" class="Symbol">}</a>
  <a id="16778" class="Symbol">→</a> <a id="16780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16765" class="Bound">x</a> <a id="16782" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15769" class="Function Operator">≐</a> <a id="16784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16767" class="Bound">y</a>
  <a id="16788" class="Symbol">→</a> <a id="16790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16767" class="Bound">y</a> <a id="16792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15769" class="Function Operator">≐</a> <a id="16794" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16769" class="Bound">z</a>
    <a id="16800" class="Comment">-----</a>
  <a id="16808" class="Symbol">→</a> <a id="16810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16765" class="Bound">x</a> <a id="16812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15769" class="Function Operator">≐</a> <a id="16814" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16769" class="Bound">z</a>
<a id="16816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16742" class="Function">trans-≐</a> <a id="16824" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16824" class="Bound">x≐y</a> <a id="16828" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16828" class="Bound">y≐z</a> <a id="16832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16832" class="Bound">P</a> <a id="16834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16834" class="Bound">Px</a>  <a id="16838" class="Symbol">=</a>  <a id="16841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16828" class="Bound">y≐z</a> <a id="16845" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16832" class="Bound">P</a> <a id="16847" class="Symbol">(</a><a id="16848" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16824" class="Bound">x≐y</a> <a id="16852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16832" class="Bound">P</a> <a id="16854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16834" class="Bound">Px</a><a id="16856" class="Symbol">)</a>{% endraw %}</pre>

Symmetry is less obvious.  We have to show that if `P x` implies `P y`
for all predicates `P`, then the implication holds the other way round
as well.
<pre class="Agda">{% raw %}<a id="sym-≐"></a><a id="17034" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17034" class="Function">sym-≐</a> <a id="17040" class="Symbol">:</a> <a id="17042" class="Symbol">∀</a> <a id="17044" class="Symbol">{</a><a id="17045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17045" class="Bound">A</a> <a id="17047" class="Symbol">:</a> <a id="17049" class="PrimitiveType">Set</a><a id="17052" class="Symbol">}</a> <a id="17054" class="Symbol">{</a><a id="17055" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17055" class="Bound">x</a> <a id="17057" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17057" class="Bound">y</a> <a id="17059" class="Symbol">:</a> <a id="17061" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17045" class="Bound">A</a><a id="17062" class="Symbol">}</a>
  <a id="17066" class="Symbol">→</a> <a id="17068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17055" class="Bound">x</a> <a id="17070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15769" class="Function Operator">≐</a> <a id="17072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17057" class="Bound">y</a>
    <a id="17078" class="Comment">-----</a>
  <a id="17086" class="Symbol">→</a> <a id="17088" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17057" class="Bound">y</a> <a id="17090" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15769" class="Function Operator">≐</a> <a id="17092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17055" class="Bound">x</a>
<a id="17094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17034" class="Function">sym-≐</a> <a id="17100" class="Symbol">{</a><a id="17101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17101" class="Bound">A</a><a id="17102" class="Symbol">}</a> <a id="17104" class="Symbol">{</a><a id="17105" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17105" class="Bound">x</a><a id="17106" class="Symbol">}</a> <a id="17108" class="Symbol">{</a><a id="17109" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17109" class="Bound">y</a><a id="17110" class="Symbol">}</a> <a id="17112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17112" class="Bound">x≐y</a> <a id="17116" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17116" class="Bound">P</a>  <a id="17119" class="Symbol">=</a>  <a id="17122" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17204" class="Function">Qy</a>
  <a id="17127" class="Keyword">where</a>
    <a id="17137" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17137" class="Function">Q</a> <a id="17139" class="Symbol">:</a> <a id="17141" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17101" class="Bound">A</a> <a id="17143" class="Symbol">→</a> <a id="17145" class="PrimitiveType">Set</a>
    <a id="17153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17137" class="Function">Q</a> <a id="17155" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17155" class="Bound">z</a> <a id="17157" class="Symbol">=</a> <a id="17159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17116" class="Bound">P</a> <a id="17161" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17155" class="Bound">z</a> <a id="17163" class="Symbol">→</a> <a id="17165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17116" class="Bound">P</a> <a id="17167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17105" class="Bound">x</a>
    <a id="17173" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17173" class="Function">Qx</a> <a id="17176" class="Symbol">:</a> <a id="17178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17137" class="Function">Q</a> <a id="17180" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17105" class="Bound">x</a>
    <a id="17186" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17173" class="Function">Qx</a> <a id="17189" class="Symbol">=</a> <a id="17191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16683" class="Function">refl-≐</a> <a id="17198" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17116" class="Bound">P</a>
    <a id="17204" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17204" class="Function">Qy</a> <a id="17207" class="Symbol">:</a> <a id="17209" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17137" class="Function">Q</a> <a id="17211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17109" class="Bound">y</a>
    <a id="17217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17204" class="Function">Qy</a> <a id="17220" class="Symbol">=</a> <a id="17222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17112" class="Bound">x≐y</a> <a id="17226" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17137" class="Function">Q</a> <a id="17228" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17173" class="Function">Qx</a>{% endraw %}</pre>
Given `x ≐ y`, a specific `P`, a proof of `P y`, we have to
construct a proof of `P x`.  To do so, we instantiate the equality
with a predicate `Q` such that `Q z` holds if `P z` implies `P x`.
The property `Q x` is trivial by reflexivity, and hence `Q y` follows
from `x ≐ y`.  But `Q y` is exactly a proof of what we require, that
`P y` implies `P x`.

We now show that Martin Löf equivalence implies
Leibniz equality, and vice versa.  In the forward direction, if we know
`x ≡ y` we need for any `P` to take evidence of `P x` to evidence of `P y`,
which is easy since equivalence of `x` and `y` implies that any proof
of `P x` is also a proof of `P y`.
<pre class="Agda">{% raw %}<a id="≡-implies-≐"></a><a id="17911" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17911" class="Function">≡-implies-≐</a> <a id="17923" class="Symbol">:</a> <a id="17925" class="Symbol">∀</a> <a id="17927" class="Symbol">{</a><a id="17928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17928" class="Bound">A</a> <a id="17930" class="Symbol">:</a> <a id="17932" class="PrimitiveType">Set</a><a id="17935" class="Symbol">}</a> <a id="17937" class="Symbol">{</a><a id="17938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17938" class="Bound">x</a> <a id="17940" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17940" class="Bound">y</a> <a id="17942" class="Symbol">:</a> <a id="17944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17928" class="Bound">A</a><a id="17945" class="Symbol">}</a>
  <a id="17949" class="Symbol">→</a> <a id="17951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17938" class="Bound">x</a> <a id="17953" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="17955" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17940" class="Bound">y</a>
    <a id="17961" class="Comment">-----</a>
  <a id="17969" class="Symbol">→</a> <a id="17971" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17938" class="Bound">x</a> <a id="17973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15769" class="Function Operator">≐</a> <a id="17975" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17940" class="Bound">y</a>
<a id="17977" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17911" class="Function">≡-implies-≐</a> <a id="17989" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17989" class="Bound">x≡y</a> <a id="17993" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17993" class="Bound">P</a>  <a id="17996" class="Symbol">=</a>  <a id="17999" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4914" class="Function">subst</a> <a id="18005" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17993" class="Bound">P</a> <a id="18007" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17989" class="Bound">x≡y</a>{% endraw %}</pre>
This direction follows from substitution, which we showed earlier.

In the reverse direction, given that for any `P` we can take a proof of `P x`
to a proof of `P y` we need to show `x ≡ y`. 
<pre class="Agda">{% raw %}<a id="≐-implies-≡"></a><a id="18227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18227" class="Function">≐-implies-≡</a> <a id="18239" class="Symbol">:</a> <a id="18241" class="Symbol">∀</a> <a id="18243" class="Symbol">{</a><a id="18244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18244" class="Bound">A</a> <a id="18246" class="Symbol">:</a> <a id="18248" class="PrimitiveType">Set</a><a id="18251" class="Symbol">}</a> <a id="18253" class="Symbol">{</a><a id="18254" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18254" class="Bound">x</a> <a id="18256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18256" class="Bound">y</a> <a id="18258" class="Symbol">:</a> <a id="18260" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18244" class="Bound">A</a><a id="18261" class="Symbol">}</a>
  <a id="18265" class="Symbol">→</a> <a id="18267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18254" class="Bound">x</a> <a id="18269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15769" class="Function Operator">≐</a> <a id="18271" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18256" class="Bound">y</a>
    <a id="18277" class="Comment">-----</a>
  <a id="18285" class="Symbol">→</a> <a id="18287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18254" class="Bound">x</a> <a id="18289" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="18291" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18256" class="Bound">y</a>
<a id="18293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18227" class="Function">≐-implies-≡</a> <a id="18305" class="Symbol">{</a><a id="18306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18306" class="Bound">A</a><a id="18307" class="Symbol">}</a> <a id="18309" class="Symbol">{</a><a id="18310" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18310" class="Bound">x</a><a id="18311" class="Symbol">}</a> <a id="18313" class="Symbol">{</a><a id="18314" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18314" class="Bound">y</a><a id="18315" class="Symbol">}</a> <a id="18317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18317" class="Bound">x≐y</a>  <a id="18322" class="Symbol">=</a>  <a id="18325" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18399" class="Function">Qy</a>
  <a id="18330" class="Keyword">where</a>
    <a id="18340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18340" class="Function">Q</a> <a id="18342" class="Symbol">:</a> <a id="18344" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18306" class="Bound">A</a> <a id="18346" class="Symbol">→</a> <a id="18348" class="PrimitiveType">Set</a>
    <a id="18356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18340" class="Function">Q</a> <a id="18358" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18358" class="Bound">z</a> <a id="18360" class="Symbol">=</a> <a id="18362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18310" class="Bound">x</a> <a id="18364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="18366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18358" class="Bound">z</a>
    <a id="18372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18372" class="Function">Qx</a> <a id="18375" class="Symbol">:</a> <a id="18377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18340" class="Function">Q</a> <a id="18379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18310" class="Bound">x</a>
    <a id="18385" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18372" class="Function">Qx</a> <a id="18388" class="Symbol">=</a> <a id="18390" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>
    <a id="18399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18399" class="Function">Qy</a> <a id="18402" class="Symbol">:</a> <a id="18404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18340" class="Function">Q</a> <a id="18406" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18314" class="Bound">y</a>
    <a id="18412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18399" class="Function">Qy</a> <a id="18415" class="Symbol">=</a> <a id="18417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18317" class="Bound">x≐y</a> <a id="18421" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18340" class="Function">Q</a> <a id="18423" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18372" class="Function">Qx</a>{% endraw %}</pre>
The proof is similar to that for symmetry of Leibniz equality. We take
`Q` to be the predicate that holds of `z` if `x ≡ z`. Then `Q x` is
trivial by reflexivity of Martin Löf equivalence, and hence `Q y`
follows from `x ≐ y`.  But `Q y` is exactly a proof of what we
require, that `x ≡ y`.

(Parts of this section are adapted from *≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*, by Andreas Abel,
Jesper Cockx, Dominique Devries, Andreas Nuyts, and Philip Wadler,
draft, 2017.)


## Universe polymorphism {#unipoly}

As we have seen, not every type belongs to `Set`, but instead every
type belongs somewhere in the hierarchy `Set₀`, `Set₁`, `Set₂`, and so on,
where `Set` abbreviates `Set₀`, and `Set₀ : Set₁`, `Set₁ : Set₂`, and so on.
The definition of equality given above is fine if we want to compare two
values of a type that belongs to `Set`, but what if we want to compare
two values of a type that belongs to `Set ℓ` for some arbitrary level `ℓ`?

The answer is _universe polymorphism_, where a definition is made
with respect to an arbitrary level `ℓ`. To make use of levels, we
first import the following.
<pre class="Agda">{% raw %}<a id="19597" class="Keyword">open</a> <a id="19602" class="Keyword">import</a> <a id="19609" href="https://agda.github.io/agda-stdlib/Level.html" class="Module">Level</a> <a id="19615" class="Keyword">using</a> <a id="19621" class="Symbol">(</a><a id="19622" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="19627" class="Symbol">;</a> <a id="19629" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#657" class="Primitive Operator">_⊔_</a><a id="19632" class="Symbol">)</a> <a id="19634" class="Keyword">renaming</a> <a id="19643" class="Symbol">(</a><a id="19644" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#627" class="Primitive">suc</a> <a id="19648" class="Symbol">to</a> <a id="19651" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#627" class="Primitive">lsuc</a><a id="19655" class="Symbol">;</a> <a id="19657" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#611" class="Primitive">zero</a> <a id="19662" class="Symbol">to</a> <a id="19665" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#611" class="Primitive">lzero</a><a id="19670" class="Symbol">)</a>{% endraw %}</pre>
Levels are isomorphic to natural numbers, and have similar constructors:

    lzero : Level
    lsuc  : Level → Level

The names `Set₀`, `Set₁`, `Set₂`, and so on, are abbreviations for

    Set lzero
    Set (lsuc lzero)
    Set (lsuc (lsuc lzero))

and so on. There is also an operator

    _⊔_ : Level → Level → Level

that given two levels returns the larger of the two.

Here is the definition of equality, generalised to an arbitrary level.
<pre class="Agda">{% raw %}<a id="20143" class="Keyword">data</a> <a id="_≡′_"></a><a id="20148" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20148" class="Datatype Operator">_≡′_</a> <a id="20153" class="Symbol">{</a><a id="20154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20154" class="Bound">ℓ</a> <a id="20156" class="Symbol">:</a> <a id="20158" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="20163" class="Symbol">}</a> <a id="20165" class="Symbol">{</a><a id="20166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20166" class="Bound">A</a> <a id="20168" class="Symbol">:</a> <a id="20170" class="PrimitiveType">Set</a> <a id="20174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20154" class="Bound">ℓ</a><a id="20175" class="Symbol">}</a> <a id="20177" class="Symbol">:</a> <a id="20179" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20166" class="Bound">A</a> <a id="20181" class="Symbol">→</a> <a id="20183" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20166" class="Bound">A</a> <a id="20185" class="Symbol">→</a> <a id="20187" class="PrimitiveType">Set</a> <a id="20191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20154" class="Bound">ℓ</a> <a id="20193" class="Keyword">where</a>
  <a id="_≡′_.refl′"></a><a id="20201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20201" class="InductiveConstructor">refl′</a> <a id="20207" class="Symbol">:</a> <a id="20209" class="Symbol">∀</a> <a id="20211" class="Symbol">{</a><a id="20212" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20212" class="Bound">x</a> <a id="20214" class="Symbol">:</a> <a id="20216" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20166" class="Bound">A</a><a id="20217" class="Symbol">}</a> <a id="20219" class="Symbol">→</a> <a id="20221" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20212" class="Bound">x</a> <a id="20223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20148" class="Datatype Operator">≡′</a> <a id="20226" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20212" class="Bound">x</a>{% endraw %}</pre>
Similarly, here is the generalised definition of symmetry.
<pre class="Agda">{% raw %}<a id="sym′"></a><a id="20311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20311" class="Function">sym′</a> <a id="20316" class="Symbol">:</a> <a id="20318" class="Symbol">∀</a> <a id="20320" class="Symbol">{</a><a id="20321" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20321" class="Bound">ℓ</a> <a id="20323" class="Symbol">:</a> <a id="20325" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="20330" class="Symbol">}</a> <a id="20332" class="Symbol">{</a><a id="20333" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20333" class="Bound">A</a> <a id="20335" class="Symbol">:</a> <a id="20337" class="PrimitiveType">Set</a> <a id="20341" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20321" class="Bound">ℓ</a><a id="20342" class="Symbol">}</a> <a id="20344" class="Symbol">{</a><a id="20345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20345" class="Bound">x</a> <a id="20347" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20347" class="Bound">y</a> <a id="20349" class="Symbol">:</a> <a id="20351" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20333" class="Bound">A</a><a id="20352" class="Symbol">}</a> <a id="20354" class="Symbol">→</a>  <a id="20357" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20345" class="Bound">x</a> <a id="20359" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20148" class="Datatype Operator">≡′</a> <a id="20362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20347" class="Bound">y</a> <a id="20364" class="Symbol">→</a> <a id="20366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20347" class="Bound">y</a> <a id="20368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20148" class="Datatype Operator">≡′</a> <a id="20371" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20345" class="Bound">x</a>
<a id="20373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20311" class="Function">sym′</a> <a id="20378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20201" class="InductiveConstructor">refl′</a> <a id="20384" class="Symbol">=</a> <a id="20386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20201" class="InductiveConstructor">refl′</a>{% endraw %}</pre>
For simplicity, we avoid universe polymorphism in the definitions given in
the text, but most definitions in the standard library, including those for
equality, are generalised to arbitrary levels as above.

Here is the generalised definition of Leibniz equality.
<pre class="Agda">{% raw %}<a id="_≐′_"></a><a id="20680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20680" class="Function Operator">_≐′_</a> <a id="20685" class="Symbol">:</a> <a id="20687" class="Symbol">∀</a> <a id="20689" class="Symbol">{</a><a id="20690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20690" class="Bound">ℓ</a> <a id="20692" class="Symbol">:</a> <a id="20694" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="20699" class="Symbol">}</a> <a id="20701" class="Symbol">{</a><a id="20702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20702" class="Bound">A</a> <a id="20704" class="Symbol">:</a> <a id="20706" class="PrimitiveType">Set</a> <a id="20710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20690" class="Bound">ℓ</a><a id="20711" class="Symbol">}</a> <a id="20713" class="Symbol">(</a><a id="20714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20714" class="Bound">x</a> <a id="20716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20716" class="Bound">y</a> <a id="20718" class="Symbol">:</a> <a id="20720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20702" class="Bound">A</a><a id="20721" class="Symbol">)</a> <a id="20723" class="Symbol">→</a> <a id="20725" class="PrimitiveType">Set</a> <a id="20729" class="Symbol">(</a><a id="20730" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#627" class="Primitive">lsuc</a> <a id="20735" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20690" class="Bound">ℓ</a><a id="20736" class="Symbol">)</a>
<a id="20738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20680" class="Function Operator">_≐′_</a> <a id="20743" class="Symbol">{</a><a id="20744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20744" class="Bound">ℓ</a><a id="20745" class="Symbol">}</a> <a id="20747" class="Symbol">{</a><a id="20748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20748" class="Bound">A</a><a id="20749" class="Symbol">}</a> <a id="20751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20751" class="Bound">x</a> <a id="20753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20753" class="Bound">y</a> <a id="20755" class="Symbol">=</a> <a id="20757" class="Symbol">∀</a> <a id="20759" class="Symbol">(</a><a id="20760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20760" class="Bound">P</a> <a id="20762" class="Symbol">:</a> <a id="20764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20748" class="Bound">A</a> <a id="20766" class="Symbol">→</a> <a id="20768" class="PrimitiveType">Set</a> <a id="20772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20744" class="Bound">ℓ</a><a id="20773" class="Symbol">)</a> <a id="20775" class="Symbol">→</a> <a id="20777" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20760" class="Bound">P</a> <a id="20779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20751" class="Bound">x</a> <a id="20781" class="Symbol">→</a> <a id="20783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20760" class="Bound">P</a> <a id="20785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20753" class="Bound">y</a>{% endraw %}</pre>
Before the signature used `Set₁` as the type of a term that includes
`Set`, whereas here the signature uses `Set (suc ℓ)` as the type of a
term that includes `Set ℓ`.

Further information on levels can be found in
the [Agda Wiki][wiki].

[wiki]: http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.UniversePolymorphism


## Standard library

Definitions similar to those in this chapter can be found in the
standard library.
<pre class="Agda">{% raw %}<a id="21249" class="Comment">-- import Relation.Binary.PropositionalEquality as Eq</a>
<a id="21303" class="Comment">-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)</a>
<a id="21367" class="Comment">-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)</a>{% endraw %}</pre>
Here the imports are shown as comments rather than code to avoid
collisions, as mentioned in the introduction.


## Unicode

This chapter uses the following unicode.

    ≡  U+2261  IDENTICAL TO (\==)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)
    ≐  U+2250  APPROACHES THE LIMIT (\.=)
    ℓ  U+2113  SCRIPT SMALL L (\ell)
