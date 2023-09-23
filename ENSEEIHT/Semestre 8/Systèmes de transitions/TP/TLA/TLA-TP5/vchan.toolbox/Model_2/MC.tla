---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_1680621280103234000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_1680621280103235000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_1680621280103236000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_1680621280103237000 == 
1..8
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1680621280103238000 ==
Len(Sent) < 6
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1680621280103241000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Tue Apr 04 17:14:40 CEST 2023 by ahamoir
