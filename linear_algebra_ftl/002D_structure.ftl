[read linear_algebra_ftl/A_Props/001A_function.ftl]

Signature. carr is a notion.
Signature. zero is a notion.
Signature. one is a notion.
Signature. add is a notion.
Signature. mul is a notion.
Signature. neg is a notion.
Signature. inv is a notion.
Signature. smul is a notion.

Signature. lang is a set.
Axiom. lang = {carr,zero,one,add,mul,neg,inv,smul}.

Definition. A structure is a function S such that Dom(S) is subset of lang.

Let S denote a structure.
Let |S| stand for S[carr].
Let 0{S} stand for S[zero].
Let 1{S} stand for S[one].
Let add{S} stand for S[add].
Let mul{S} stand for S[mul].
Let neg{S} stand for S[neg].
Let inv{S} stand for S[inv].
Let smul{S} stand for S[smul].

Let a +{S} b stand for add{S}[(a,b)].
Let a *{S} b stand for mul{S}[(a,b)].
Let ~{S} a stand for neg{S}[a].
Let a -{S} b stand for add{S}[(a,neg{S}[b])].
Let a /{S} b stand for mul{S}[(a,inv{S}[b])].
Let a @{S} b stand for smul{S}[(a,b)].
Let a < S stand for a << |S|.
Let a < S* stand for a << |S|\{0{S}}.

Let (S has a) stand for (a << Dom(S)).
Let (S has a,b) stand for (a,b << Dom(S)).
Let (S has a,b,c) stand for (a,b,c << Dom(S)).
Let (S has a,b,c,d) stand for (a,b,c,d << Dom(S)).
Let (S has a,b,c,d,e) stand for (a,b,c,d,e << Dom(S)).
Let (S has a,b,c,d,e,f) stand for (a,b,c,d,e,f << Dom(S)).
Let (S has a,b,c,d,e,f,g) stand for (a,b,c,d,e,f,g << Dom(S)).
Let (S has a,b,c,d,e,f,g,h) stand for (a,b,c,d,e,f,g,h << Dom(S)).
