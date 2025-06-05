# TLA+ Spec Inference from Java: A Step-by-Step Guide

## Phase 1: Master the Fundamentals (TLA+ & Java Parsing)

### Step 1: Get Proficient with TLA+ and TLC

#### Install TLA+ Toolbox
- Download from: http://tla.msr-inria.fr/tla/toolbox.html
- Explore the examples that come with it

#### Go Through Lamport's "Specifying Systems"
- Focus on states, actions, invariants
- Understand Init and Next definitions
- Practice with simple concurrent systems:
  - 2-slot buffer
  - Peterson's algorithm
  - Producer-Consumer example

#### Verify Properties with TLC
- Safety properties (mutual exclusion, no buffer overflow)
- Liveness properties (eventual message processing)
- Debug with counterexamples

#### Explore Apalache (Optional)
- Install from: https://apalache.informal.systems/
- Try running existing TLA+ specs
- Compare results with TLC

### Step 2: Learn Java Parsing with JavaParser

#### Set up Java Project
```xml
<dependency>
    <groupId>com.github.javaparser</groupId>
    <artifactId>javaparser-core</artifactId>
    <version>3.25.10</version>
</dependency>
```

#### Parse Simple Java Code
```java
public class MySimpleProgram {
    public static void main(String[] args) {
        int x = 10;
        int y = x + 5;
        if (y > 10) {
            System.out.println("Greater than 10");
        } else {
            System.out.println("Not greater than 10");
        }
    }
}
```

#### AST Explorer Implementation
```java
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

import java.io.FileInputStream;
import java.io.FileNotFoundException;

public class AstExplorer {
    public static void main(String[] args) throws FileNotFoundException {
        String filePath = "src/main/java/MySimpleProgram.java";
        FileInputStream in = new FileInputStream(filePath);
        CompilationUnit cu = StaticJavaParser.parse(in);
        
        System.out.println("Full AST:\n" + cu.toString());
        System.out.println("\nMethods found:");
        cu.accept(new MethodVisitor(), null);
    }

    private static class MethodVisitor extends VoidVisitorAdapter<Void> {
        @Override
        public void visit(MethodDeclaration n, Void arg) {
            System.out.println("  Method name: " + n.getName());
            n.getBody().ifPresent(body -> {
                body.getStatements().forEach(stmt -> {
                    System.out.println("    Statement: " + stmt.getClass().getSimpleName());
                    if (stmt instanceof ExpressionStmt) {
                        System.out.println("      Expression: " + ((ExpressionStmt) stmt).getExpression());
                    }
                });
            });
            super.visit(n, arg);
        }
    }
}
```

## Phase 2: From Java AST to Basic TLA+ Model

### Step 3: Minimal Java to TLA+ Conversion

#### Define TLA+ State
```tla
VARIABLE x, y, pc
```

#### Translate Java Assignments
```java
// Java
int x = 10;
y = x + 5;

// TLA+
x' = 10
y' = x + 5
```

#### Translate If Statements
```java
// Java
if (y > 10) {
    // true branch
} else {
    // false branch
}

// TLA+
Next ==
  \/ (y > 10 /\ (* true branch actions *))
  \/ (y <= 10 /\ (* false branch actions *))
  /\ pc' = pc + 1
```

### Step 4: Program Counter in TLA+

#### Basic Structure
```tla
VARIABLE x, y, pc

Init == x = 0 /\ y = 0 /\ pc = 0

Next == Step0 \/ Step1 \/ Step2
Step0 == (pc = 0 /\ x' = 10 /\ pc' = 1 /\ UNCHANGED y)
Step1 == (pc = 1 /\ y' = x + 5 /\ pc' = 2 /\ UNCHANGED x)
```

### Step 5: Basic Model Checking

#### TLC Configuration
1. Open generated .tla file in TLA+ Toolbox
2. Create new model
3. Define Init and Next predicates
4. Add invariants:
   ```tla
   Invariant == x >= 0 /\ y >= 0
   ```
5. Run TLC and analyze results

## Phase 3: Advanced Features and Pitfalls

### Step 6: Variable Handling

#### Scope and Types
```tla
VARIABLE ThreadVars, Heap

ThreadVars == [threadId \in Threads |-> 
              [frameId \in Nat |-> 
               [varName \in VarNames |-> value]]]

Heap == [objId \in ObjectIds |-> 
         [fieldName \in FieldNames |-> value]]
```

### Step 7: Loops and Method Calls

#### Loop Translation
```java
// Java
while (x > 0) {
    x = x - 1;
}

// TLA+
LoopStep == 
  /\ pc = loopStart
  /\ x > 0
  /\ x' = x - 1
  /\ pc' = loopStart
  /\ UNCHANGED <<other vars>>

ExitLoop ==
  /\ pc = loopStart
  /\ x <= 0
  /\ pc' = loopEnd
  /\ UNCHANGED <<other vars>>
```

#### Method Call Stack
```tla
VARIABLE CallStack

CallStack == [frameId \in Nat |-> 
             [pc |-> programCounter,
              locals |-> localVariables,
              params |-> parameters]]
```

### Step 8: Concurrency

#### Thread Management
```tla
VARIABLE threads, sharedMemory

threads == [t \in Threads |-> 
           [pc |-> programCounter,
            locals |-> localVariables]]

Next == \E t \in Threads : ThreadStep(t)
```

#### Basic Synchronization
```tla
VARIABLE lock

AcquireLock ==
  /\ lock = FALSE
  /\ lock' = TRUE
  /\ UNCHANGED <<other vars>>

ReleaseLock ==
  /\ lock = TRUE
  /\ lock' = FALSE
  /\ UNCHANGED <<other vars>>
```

## Practical Examples

### Example 1: Simple Counter
```java
// Java
public class Counter {
    private int count = 0;
    
    public void increment() {
        count++;
    }
    
    public int getCount() {
        return count;
    }
}
```

```tla
// TLA+
VARIABLE count, pc

Init == count = 0 /\ pc = 0

Next == Increment \/ GetCount

Increment ==
  /\ pc = 0
  /\ count' = count + 1
  /\ pc' = 0

GetCount ==
  /\ pc = 1
  /\ UNCHANGED count
  /\ pc' = 1
```

### Example 2: Producer-Consumer
```java
// Java
public class Buffer {
    private int[] buffer = new int[2];
    private int in = 0, out = 0;
    
    public void put(int item) {
        buffer[in] = item;
        in = (in + 1) % 2;
    }
    
    public int get() {
        int item = buffer[out];
        out = (out + 1) % 2;
        return item;
    }
}
```

```tla
// TLA+
VARIABLE buffer, in, out, pc

Init == 
  /\ buffer = [i \in 0..1 |-> 0]
  /\ in = 0
  /\ out = 0
  /\ pc = 0

Next == Put \/ Get

Put ==
  /\ pc = 0
  /\ buffer' = [buffer EXCEPT ![in] = item]
  /\ in' = (in + 1) % 2
  /\ pc' = 0
  /\ UNCHANGED out

Get ==
  /\ pc = 1
  /\ item' = buffer[out]
  /\ out' = (out + 1) % 2
  /\ pc' = 1
  /\ UNCHANGED <<buffer, in>>
```

## Best Practices and Tips

1. **Start Small**
   - Begin with simple integer assignments
   - Add control structures one at a time
   - Test thoroughly at each step

2. **Use TLC Effectively**
   - Start with small state spaces
   - Add invariants incrementally
   - Use symmetry sets for concurrent models

3. **Debugging Strategies**
   - Use TLC's error traces
   - Add temporary invariants
   - Simplify complex expressions

4. **Performance Considerations**
   - Use Apalache for larger models
   - Optimize state space with symmetry
   - Consider using TLA+ modules for reuse

## Resources

1. **Official Documentation**
   - [TLA+ Homepage](https://lamport.azurewebsites.net/tla/tla.html)
   - [TLA+ Toolbox](http://tla.msr-inria.fr/tla/toolbox.html)
   - [Apalache](https://apalache.informal.systems/)

2. **Books and Tutorials**
   - "Specifying Systems" by Leslie Lamport
   - "Practical TLA+" by Hillel Wayne
   - [TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html)

3. **Community**
   - [TLA+ Google Group](https://groups.google.com/g/tlaplus)
   - [Stack Overflow TLA+ tag](https://stackoverflow.com/questions/tagged/tla+)
   - [TLA+ GitHub Discussions](https://github.com/tlaplus/tlaplus/discussions) 