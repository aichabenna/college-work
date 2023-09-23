---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_168062010573797000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_168062010573798000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_168062010573799000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_1680620105737100000 == 
1..5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1680620105737101000 ==
Len(Sent) < 4
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1680620105737104000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Tue Apr 04 16:55:05 CEST 2023 by ahamoir
