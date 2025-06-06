package com.tlajvm.parser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.body.Parameter;

import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Path;
import java.util.*;

public class TlaSpecGenerator {
    private static final Logger log = LoggerFactory.getLogger(TlaSpecGenerator.class);
    private final StringBuilder specBuilder = new StringBuilder();
    private final List<String> variables = new ArrayList<>();
    private final Map<String, String> variableTypes = new HashMap<>();
    private int pcCounter = 0;
    private final Set<String> invariants = new HashSet<>();
    private final Set<String> temporalProperties = new HashSet<>();

    public void generateSpec(CompilationUnit cu, Path outputPath) {
        // Collect all field declarations before building the TLA+ specification
        collectFieldDeclarations(cu);
        
        // Start building the TLA+ specification
        specBuilder.append("---- MODULE ").append(cu.getType(0).getNameAsString()).append(" ----\n\n");
        
        // Add EXTENDS clause
        specBuilder.append("EXTENDS Naturals, Sequences, TLC\n\n");
        
        // Add variables section
        specBuilder.append("VARIABLE pc\n");
        variables.forEach(v -> specBuilder.append("VARIABLE ").append(v).append("\n"));
        specBuilder.append("\n");
        
        // Add Init predicate
        specBuilder.append("Init ==\n");
        specBuilder.append("  /\\ pc = 0\n");
        variables.forEach(v -> {
            String type = variableTypes.getOrDefault(v, "0");
            if (v.endsWith("[]")) {
                String baseName = v.substring(0, v.length() - 2);
                specBuilder.append("  /\\ ").append(baseName).append(" = [i \\in 1..N | ").append(type).append("]\n");
            } else {
                specBuilder.append("  /\\ ").append(v).append(" = ").append(type).append("\n");
            }
        });
        specBuilder.append("\n");
        
        // Add Next predicate
        specBuilder.append("Next ==\n");
        specBuilder.append(generateNextPredicate(cu));
        specBuilder.append("\n\n");
        
        // Add invariants
        specBuilder.append("Invariants ==\n");
        specBuilder.append("  /\\ pc >= 0\n");
        variables.forEach(v -> {
            if (v.endsWith("[]")) {
                String baseName = v.substring(0, v.length() - 2);
                specBuilder.append("  /\\ ").append(baseName).append(" \\in [1..N -> Nat]\n");
            } else {
                String type = variableTypes.getOrDefault(v, "0");
                if (type.equals("FALSE")) {
                    specBuilder.append("  /\\ ").append(v).append(" \\in BOOLEAN\n");
                } else {
                    specBuilder.append("  /\\ ").append(v).append(" \\in Nat\n");
                }
            }
        });
        specBuilder.append("\n");
        
        // Add temporal properties
        specBuilder.append("TemporalProperties ==\n");
        specBuilder.append("  /\\ WF_vars(pc)\n");
        variables.forEach(v -> specBuilder.append("  /\\ WF_vars(").append(v).append(")\n"));
        specBuilder.append("\n");
        
        // Add deadlock freedom property
        specBuilder.append("DeadlockFreedom ==\n");
        specBuilder.append("  WF_vars(pc)\n\n");
        
        // Add module end
        specBuilder.append("====");
        
        // Write the specification to a file
        try (FileWriter writer = new FileWriter(outputPath.toFile())) {
            writer.write(specBuilder.toString());
            log.info("TLA+ specification written to: {}", outputPath);
            System.out.println("[INFO] TLA+ specification written to: " + outputPath);
        } catch (IOException e) {
            log.error("Error writing TLA+ specification", e);
            System.out.println("[ERROR] Could not write TLA+ specification to file. Printing to stdout:\n");
            System.out.println(specBuilder.toString());
        }
    }

    private String generateNextPredicate(CompilationUnit cu) {
        StringBuilder nextBuilder = new StringBuilder();
        cu.accept(new MethodVisitor(), nextBuilder);
        return nextBuilder.toString();
    }

    private class MethodVisitor extends VoidVisitorAdapter<StringBuilder> {
        private final Map<String, MethodDeclaration> methodMap = new HashMap<>();

        @Override
        public void visit(MethodDeclaration n, StringBuilder nextBuilder) {
            // Collect all method declarations for inlining
            methodMap.put(n.getNameAsString(), n);
            n.getBody().ifPresent(body -> {
                body.getStatements().forEach(stmt -> {
                    if (stmt instanceof ExpressionStmt) {
                        handleExpressionStmt((ExpressionStmt) stmt, nextBuilder);
                    } else if (stmt instanceof WhileStmt) {
                        handleWhileStmt((WhileStmt) stmt, nextBuilder);
                    } else if (stmt instanceof ForStmt) {
                        handleForStmt((ForStmt) stmt, nextBuilder);
                    } else if (stmt instanceof IfStmt) {
                        handleIfStmt((IfStmt) stmt, nextBuilder);
                    } else if (stmt instanceof BlockStmt) {
                        handleBlockStmt((BlockStmt) stmt, nextBuilder);
                    }
                });
            });
            super.visit(n, nextBuilder);
        }

        private void handleExpressionStmt(ExpressionStmt stmt, StringBuilder nextBuilder) {
            String expr = stmt.getExpression().toString();
            // Handle method calls
            if (stmt.getExpression() instanceof MethodCallExpr) {
                MethodCallExpr call = (MethodCallExpr) stmt.getExpression();
                String methodName = call.getNameAsString();
                if (methodMap.containsKey(methodName)) {
                    MethodDeclaration method = methodMap.get(methodName);
                    // Only inline simple methods (no recursion, no control flow)
                    if (method.getBody().isPresent()) {
                        for (Statement s : method.getBody().get().getStatements()) {
                            if (s instanceof ExpressionStmt) {
                                handleExpressionStmt((ExpressionStmt) s, nextBuilder);
                            }
                        }
                    }
                    return;
                }
            }
            // Extract variable name and value
            if (expr.contains("=")) {
                String[] parts = expr.split("=");
                String varName = parts[0].trim();
                String value = parts[1].trim();
                // Add variable to list if not already present
                if (!variables.contains(varName)) {
                    variables.add(varName);
                    // Try to infer type
                    if (value.contains("true") || value.contains("false")) {
                        variableTypes.put(varName, "FALSE");
                    } else if (value.matches("-?\\d+")) {
                        variableTypes.put(varName, "0");
                    }
                }
                // Add step to Next predicate
                addStep(varName, value, nextBuilder);
            }
        }

        private void handleWhileStmt(WhileStmt stmt, StringBuilder nextBuilder) {
            String condition = stmt.getCondition().toString();
            int loopStart = pcCounter;
            
            // Add loop condition check
            nextBuilder.append("  \\E Step").append(pcCounter).append(" ==\n");
            nextBuilder.append("    /\\ pc = ").append(pcCounter).append("\n");
            nextBuilder.append("    /\\ ").append(condition).append("\n");
            nextBuilder.append("    /\\ pc' = ").append(pcCounter + 1).append("\n");
            nextBuilder.append("    /\\ UNCHANGED <<");
            variables.forEach(v -> nextBuilder.append(v).append(", "));
            nextBuilder.setLength(nextBuilder.length() - 2);
            nextBuilder.append(">>\n");
            pcCounter++;
            
            // Add loop body
            stmt.getBody().accept(this, nextBuilder);
            
            // Add loop end
            nextBuilder.append("  \\E Step").append(pcCounter).append(" ==\n");
            nextBuilder.append("    /\\ pc = ").append(pcCounter).append("\n");
            nextBuilder.append("    /\\ ~(").append(condition).append(")\n");
            nextBuilder.append("    /\\ pc' = ").append(pcCounter + 1).append("\n");
            nextBuilder.append("    /\\ UNCHANGED <<");
            variables.forEach(v -> nextBuilder.append(v).append(", "));
            nextBuilder.setLength(nextBuilder.length() - 2);
            nextBuilder.append(">>\n");
            pcCounter++;
        }

        private void handleIfStmt(IfStmt stmt, StringBuilder nextBuilder) {
            String condition = stmt.getCondition().toString();
            int ifStart = pcCounter;
            
            // Add if condition check
            nextBuilder.append("  \\E Step").append(pcCounter).append(" ==\n");
            nextBuilder.append("    /\\ pc = ").append(pcCounter).append("\n");
            nextBuilder.append("    /\\ ").append(condition).append("\n");
            nextBuilder.append("    /\\ pc' = ").append(pcCounter + 1).append("\n");
            nextBuilder.append("    /\\ UNCHANGED <<");
            variables.forEach(v -> nextBuilder.append(v).append(", "));
            nextBuilder.setLength(nextBuilder.length() - 2);
            nextBuilder.append(">>\n");
            pcCounter++;
            
            // Add then branch
            stmt.getThenStmt().accept(this, nextBuilder);
            
            // Add else branch if present
            if (stmt.getElseStmt().isPresent()) {
                nextBuilder.append("  \\E Step").append(pcCounter).append(" ==\n");
                nextBuilder.append("    /\\ pc = ").append(ifStart).append("\n");
                nextBuilder.append("    /\\ ~(").append(condition).append(")\n");
                nextBuilder.append("    /\\ pc' = ").append(pcCounter + 1).append("\n");
                nextBuilder.append("    /\\ UNCHANGED <<");
                variables.forEach(v -> nextBuilder.append(v).append(", "));
                nextBuilder.setLength(nextBuilder.length() - 2);
                nextBuilder.append(">>\n");
                pcCounter++;
                
                stmt.getElseStmt().get().accept(this, nextBuilder);
            }
        }

        private void handleBlockStmt(BlockStmt stmt, StringBuilder nextBuilder) {
            stmt.getStatements().forEach(s -> {
                if (s instanceof ExpressionStmt) {
                    handleExpressionStmt((ExpressionStmt) s, nextBuilder);
                } else if (s instanceof WhileStmt) {
                    handleWhileStmt((WhileStmt) s, nextBuilder);
                } else if (s instanceof IfStmt) {
                    handleIfStmt((IfStmt) s, nextBuilder);
                } else if (s instanceof BlockStmt) {
                    handleBlockStmt((BlockStmt) s, nextBuilder);
                }
            });
        }

        private void handleForStmt(ForStmt stmt, StringBuilder nextBuilder) {
            // Convert for-loop to equivalent while-loop
            // for(init; compare; update) body
            // becomes:
            //   init;
            //   while(compare) { body; update; }
            if (stmt.getInitialization().size() > 0) {
                for (com.github.javaparser.ast.expr.Expression init : stmt.getInitialization()) {
                    if (init.isAssignExpr()) {
                        // Wrap assignment as ExpressionStmt for reuse
                        handleExpressionStmt(new ExpressionStmt(init.asAssignExpr()), nextBuilder);
                    }
                }
            }
            String condition = stmt.getCompare().map(Object::toString).orElse("TRUE");
            int loopStart = pcCounter;
            // Add loop condition check
            nextBuilder.append("  \\E Step").append(pcCounter).append(" ==\n");
            nextBuilder.append("    /\\ pc = ").append(pcCounter).append("\n");
            nextBuilder.append("    /\\ ").append(condition).append("\n");
            nextBuilder.append("    /\\ pc' = ").append(pcCounter + 1).append("\n");
            nextBuilder.append("    /\\ UNCHANGED <<");
            variables.forEach(v -> nextBuilder.append(v).append(", "));
            nextBuilder.setLength(nextBuilder.length() - 2);
            nextBuilder.append(">>\n");
            pcCounter++;
            // Add loop body
            stmt.getBody().accept(this, nextBuilder);
            // Add update
            for (com.github.javaparser.ast.expr.Expression update : stmt.getUpdate()) {
                if (update.isAssignExpr()) {
                    handleExpressionStmt(new ExpressionStmt(update.asAssignExpr()), nextBuilder);
                }
            }
            // Add loop end
            nextBuilder.append("  \\E Step").append(pcCounter).append(" ==\n");
            nextBuilder.append("    /\\ pc = ").append(pcCounter).append("\n");
            nextBuilder.append("    /\\ ~(").append(condition).append(")\n");
            nextBuilder.append("    /\\ pc' = ").append(pcCounter + 1).append("\n");
            nextBuilder.append("    /\\ UNCHANGED <<");
            variables.forEach(v -> nextBuilder.append(v).append(", "));
            nextBuilder.setLength(nextBuilder.length() - 2);
            nextBuilder.append(">>\n");
            pcCounter++;
        }

        private void addStep(String varName, String value, StringBuilder nextBuilder) {
            nextBuilder.append("  \\E Step").append(pcCounter).append(" ==\n");
            nextBuilder.append("    /\\ pc = ").append(pcCounter).append("\n");
            nextBuilder.append("    /\\ ").append(varName).append("' = ").append(value).append("\n");
            nextBuilder.append("    /\\ pc' = ").append(pcCounter + 1).append("\n");
            nextBuilder.append("    /\\ UNCHANGED <<");
            variables.stream()
                    .filter(v -> !v.equals(varName))
                    .forEach(v -> nextBuilder.append(v).append(", "));
            nextBuilder.setLength(nextBuilder.length() - 2);
            nextBuilder.append(">>\n");
            pcCounter++;
        }
    }

    public void collectFieldDeclarations(CompilationUnit cu) {
        cu.findAll(FieldDeclaration.class).forEach(field -> {
            field.getVariables().forEach(var -> {
                String name = var.getNameAsString();
                if (!variables.contains(name)) {
                    variables.add(name);
                    // Infer type
                    String type = field.getElementType().asString();
                    if (type.equals("boolean")) {
                        variableTypes.put(name, "FALSE");
                    } else if (type.equals("int")) {
                        variableTypes.put(name, "0");
                    } else if (type.endsWith("[]")) {
                        // Handle array types
                        variables.add(name + "[]");
                        variableTypes.put(name + "[]", "FALSE");
                    } else {
                        variableTypes.put(name, "0");
                    }
                }
            });
        });
    }
} 