## Workflow
- Def **Inv** = **MsgInv** /\ **AccInv**
- Proving  **MsgInv** /\ **AccInv** $\Rightarrow$ Consistency
- Proving **Spec** $\Rightarrow$ **Inv** 

## DONE
- [x] Def **Inv** = **MsgInv** /\ **AccInv**
- [x] Proving **MsgInv** /\ **AccInv** $\Rightarrow$ Consistency

## TODO 
- [ ] Proving **Spec** $\Rightarrow$ **Inv** 
  - [x] Proving  **MsgInv** /\ **AccInv** $\Rightarrow$ **SafeAtStable**
    - [x] Prepare => SafeAtStable
    - [x] Accept => SafeAtStable
    - [x] OnMessage => SafeAtStable
  - [ ] Proving **Spec** $\Rightarrow$ **Inv**
    - [x] Init => Inv'
    - [ ] Next => Inv'
      - [x] Next => TypeOK'
        - [x] Prepare => TypeOK'
        - [x] Accept => TypeOK'
        - [x] OnMessage => TypeOK'
      - [ ] Next => AccInv'
        - [x] Prepare => AccInv'
        - [ ] Accept => AccInv'
        - [ ] OnMessage => AccInv'
      - [x] Next => MsgInv'
        - [x] Prepare => MsgInv'
        - [x] Accept => MsgInv'
        - [x] OnMessage => MsgInv'
