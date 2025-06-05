package com.tlajvm.parser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import lombok.extern.slf4j.Slf4j;

import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Path;
import java.util.*;

@Slf4j
public class TlaSpecGenerator {
    private static final org.slf4j.Logger log = org.slf4j.LoggerFactory.getLogger(TlaSpecGenerator.class);
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
        specBuilder.append("EXTENDS Naturals, Sequences\n\n");
        
        // Add variables section
        specBuilder.append("VARIABLE pc\n");
        variables.forEach(v -> specBuilder.append("VARIABLE ").append(v).append("\n"));
        specBuilder.append("\n");
        
        // Add Init predicate
        specBuilder.append("Init ==\n");
        specBuilder.append("  /\\ pc = 0\n");
        variables.forEach(v -> {
            String type = variableTypes.getOrDefault(v, "0");
            specBuilder.append("  /\\ ").append(v).append(" = ").append(type).append("\n");
        });
        specBuilder.append("\n");
        
        // Add Next predicate
        specBuilder.append("Next ==\n");
        specBuilder.append("  \\/ ").append(generateNextPredicate(cu)).append("\n\n");
        
        // Add invariants
        if (!invariants.isEmpty()) {
            specBuilder.append("Invariants ==\n");
            invariants.forEach(inv -> specBuilder.append("  /\\ ").append(inv).append("\n"));
            specBuilder.append("\n");
        }
        
        // Add temporal properties
        if (!temporalProperties.isEmpty()) {
            specBuilder.append("TemporalProperties ==\n");
            temporalProperties.forEach(prop -> specBuilder.append("  /\\ ").append(prop).append("\n"));
            specBuilder.append("\n");
        }
        
        // Add module end
        specBuilder.append("====");
        
        // Write the specification to a file
        try (FileWriter writer = new FileWriter(outputPath.toFile())) {
            writer.write(specBuilder.toString());
            log.info("TLA+ specification written to: {}", outputPath);
        } catch (IOException e) {
            log.error("Error writing TLA+ specification", e);
        }
    }

    private String generateNextPredicate(CompilationUnit cu) {
        StringBuilder nextBuilder = new StringBuilder();
        cu.accept(new MethodVisitor(), nextBuilder);
        return nextBuilder.toString();
    }

    private class MethodVisitor extends VoidVisitorAdapter<StringBuilder> {
        @Override
        public void visit(MethodDeclaration n, StringBuilder nextBuilder) {
            n.getBody().ifPresent(body -> {
                body.getStatements().forEach(stmt -> {
                    if (stmt instanceof ExpressionStmt) {
                        handleExpressionStmt((ExpressionStmt) stmt, nextBuilder);
                    } else if (stmt instanceof WhileStmt) {
                        handleWhileStmt((WhileStmt) stmt, nextBuilder);
                    } else if (stmt instanceof IfStmt) {
                        handleIfStmt((IfStmt) stmt, nextBuilder);
                    }
                });
            });
            super.visit(n, nextBuilder);
        }

        private void handleExpressionStmt(ExpressionStmt stmt, StringBuilder nextBuilder) {
            String expr = stmt.getExpression().toString();
            
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
            nextBuilder.append("Step").append(pcCounter).append(" ==\n");
            nextBuilder.append("  /\\ pc = ").append(pcCounter).append("\n");
            nextBuilder.append("  /\\ ").append(condition).append("\n");
            nextBuilder.append("  /\\ pc' = ").append(pcCounter + 1).append("\n");
            nextBuilder.append("  /\\ UNCHANGED <<");
            variables.forEach(v -> nextBuilder.append(v).append(", "));
            nextBuilder.setLength(nextBuilder.length() - 2);
            nextBuilder.append(">>\n");
            pcCounter++;
            
            // Add loop body
            stmt.getBody().accept(this, nextBuilder);
            
            // Add loop end
            nextBuilder.append("Step").append(pcCounter).append(" ==\n");
            nextBuilder.append("  /\\ pc = ").append(pcCounter).append("\n");
            nextBuilder.append("  /\\ ~(").append(condition).append(")\n");
            nextBuilder.append("  /\\ pc' = ").append(pcCounter + 1).append("\n");
            nextBuilder.append("  /\\ UNCHANGED <<");
            variables.forEach(v -> nextBuilder.append(v).append(", "));
            nextBuilder.setLength(nextBuilder.length() - 2);
            nextBuilder.append(">>\n");
            pcCounter++;
            
            // Add invariant for loop termination
            invariants.add("WF_vars(pc)");
            temporalProperties.add("<>[](pc > " + loopStart + " => pc > " + pcCounter + ")");
        }

        private void handleIfStmt(IfStmt stmt, StringBuilder nextBuilder) {
            String condition = stmt.getCondition().toString();
            int ifStart = pcCounter;
            
            // Add if condition check
            nextBuilder.append("Step").append(pcCounter).append(" ==\n");
            nextBuilder.append("  /\\ pc = ").append(pcCounter).append("\n");
            nextBuilder.append("  /\\ ").append(condition).append("\n");
            nextBuilder.append("  /\\ pc' = ").append(pcCounter + 1).append("\n");
            nextBuilder.append("  /\\ UNCHANGED <<");
            variables.forEach(v -> nextBuilder.append(v).append(", "));
            nextBuilder.setLength(nextBuilder.length() - 2);
            nextBuilder.append(">>\n");
            pcCounter++;
            
            // Add then branch
            stmt.getThenStmt().accept(this, nextBuilder);
            
            // Add else branch if present
            if (stmt.getElseStmt().isPresent()) {
                nextBuilder.append("Step").append(pcCounter).append(" ==\n");
                nextBuilder.append("  /\\ pc = ").append(ifStart).append("\n");
                nextBuilder.append("  /\\ ~(").append(condition).append(")\n");
                nextBuilder.append("  /\\ pc' = ").append(pcCounter + 1).append("\n");
                nextBuilder.append("  /\\ UNCHANGED <<");
                variables.forEach(v -> nextBuilder.append(v).append(", "));
                nextBuilder.setLength(nextBuilder.length() - 2);
                nextBuilder.append(">>\n");
                pcCounter++;
                
                stmt.getElseStmt().get().accept(this, nextBuilder);
            }
        }

        private void addStep(String varName, String value, StringBuilder nextBuilder) {
            nextBuilder.append("Step").append(pcCounter).append(" ==\n");
            nextBuilder.append("  /\\ pc = ").append(pcCounter).append("\n");
            nextBuilder.append("  /\\ ").append(varName).append("' = ").append(value).append("\n");
            nextBuilder.append("  /\\ pc' = ").append(pcCounter + 1).append("\n");
            nextBuilder.append("  /\\ UNCHANGED <<");
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
                    } else {
                        variableTypes.put(name, "0");
                    }
                }
            });
        });
    }
} 