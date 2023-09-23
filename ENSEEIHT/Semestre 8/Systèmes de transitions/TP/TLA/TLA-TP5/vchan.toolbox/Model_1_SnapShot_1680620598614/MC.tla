---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_1680620595577190000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_1680620595577191000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_1680620595577192000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_1680620595577193000 == 
1..5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1680620595577194000 ==
Len(Sent) < 4
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1680620595578197000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Tue Apr 04 17:03:15 CEST 2023 by ahamoir
