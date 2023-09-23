---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_1680621274336223000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_1680621274336224000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_1680621274336225000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_1680621274336226000 == 
1..5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1680621274336227000 ==
Len(Sent) < 4
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1680621274336230000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Tue Apr 04 17:14:34 CEST 2023 by ahamoir
