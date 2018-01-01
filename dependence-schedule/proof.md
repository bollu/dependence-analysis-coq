### Defn. Program

```hs
Grammar
-------

Program := [Stmt]
Value := Id | Num
Stmt := X <- Read ix  | Write ix (Value)
```

### Defn. Schedule

A schedule S is a mapping from program statements to time points.
```hs
type Schedule =  Stmt -> Time
```

### Defn. RAW Dependence

RAW Dependence is a relation between the reads and writes of a program.

### Defn, Dependence Satisfaction

A schedule `S` satifies a raw dependence `D` if `∀(x, y) ∈ D, S(x) <= S(y)`.

### Defn. Program State

the program state is a function from `Ix` to `Num`. It models the current state
of memory.

```hs
type Memory = Ix -> Num
type Bindings = Id -> Num
data State = State { memory :: Memory, bindings :: Bindings }
```

### Schedule induced transition
Every schedule `S` induces a transition function `Transition(S) :: State -> State`

### Construction of Schedule induced transition:


```hs
programFromSchedule :: Schedule -> Program
programFromSchedule S = domain of S ordered by S.
                    = sortBy S (domain S)


getValNumber :: Bindings -> Value -> Num#
getValNumber (Num n) = n
getValNumber (Id x) = bindings x
semanticsStmtMemory :: Stmt -> Bindings -> Memory -> Memory
semanticsStmtMemory (Read id ix) = identity
semanticsStmtMemory (Write wix val) memold =
    \ix -> if wix == ix
            then getValNumber val
            else (memold ix)


semanticsStmtBindings :: Stmt -> Memory -> Bindings -> Bindings
semanticsStmtBindings (Read bindingid ix) mem bsold =
    \id -> if id == bindingid
            then (mem ix) -- if a read is coming for our ID, read the state of memory and return the value.
            else bsold id

```

### Theorem 1: semanticsProgram [Write ix val0; Write ix val1] == semanticsProgram [Write ix val1];

```
Proof:
<will work, just need to go through derivation
```

### Theorem 2: `getValNumber (Var id)` on program state [Write ix v0; id <- Read ix] is v0.
```
Proof:
ditto
```



### RAW dependences:
 ```
 RAW(Schedule) =  { (r, w) |
    r, w ∈ domain(Schedule),
    Schedule(w) < Schedule(r),
    ix(r) == ix(w),
    ¬∃ wmid, schedule(w) < schedule(wmid) < schedule(r), ix(r) == ix(wmid)
    -- This ensures that we get the shortest possible dep. vectors.
}
```

 RAW is a dependence (obvious)


 ### Theorem. 
 ∀S', semanticsProgram(S') == semanticsProgram(S) if S' satisfies RAW(S)

 ####### Proof.

 Induction on program length.
 Length 0: obvious.
 Length n: assumed.
 Length (n + 1):


Look at program till n. We assume that semantics hold.
Now look at (n + 1)th instr.

It can only be read or write.
If Read:

```
semanticsProgram(S) = { value of last write into read ix }

semanticsProgram(S'):
    since S' satisfies RAW,
    w < r, so w has happened before.
    Also, there does not exist a w'. So, value read will be equal to last value written.
```

If Write
```
semanticsProgram(S) = { value of the write }

semanticsProgram(S'):
    if write is write an immediate value, trivial
    if write is writing a value from a ID, semantics till here agree, so ID has
    same value. Hence, semanticsProgram must agree.
```

