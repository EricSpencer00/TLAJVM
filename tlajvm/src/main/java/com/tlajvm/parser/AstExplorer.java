package com.tlajvm.parser;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import lombok.extern.slf4j.Slf4j;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;

@Slf4j
public class AstExplorer {
    public static void main(String[] args) {
        try {
            // Get the path to the example Java file
            Path filePath = Paths.get("src", "main", "java", "com", "tlajvm", "parser", "MySimpleProgram.java");
            Path tlaPath = Paths.get("src", "main", "resources", "MySimpleProgram.tla");
            
            // Parse the Java file
            try (FileInputStream in = new FileInputStream(filePath.toFile())) {
                CompilationUnit cu = StaticJavaParser.parse(in);
                
                // Explore the AST
                log.info("Full AST:\n{}", cu);
                log.info("\nMethods found:");
                cu.accept(new MethodVisitor(), null);
                
                // Generate TLA+ specification
                log.info("\nGenerating TLA+ specification...");
                TlaSpecGenerator generator = new TlaSpecGenerator();
                generator.generateSpec(cu, tlaPath);
                log.info("TLA+ specification generated at: {}", tlaPath);
            }
        } catch (FileNotFoundException e) {
            log.error("Could not find the Java file to parse", e);
        } catch (IOException e) {
            log.error("Error reading or writing files", e);
        }
    }

    private static class MethodVisitor extends VoidVisitorAdapter<Void> {
        @Override
        public void visit(MethodDeclaration n, Void arg) {
            log.info("  Method name: {}", n.getName());
            n.getBody().ifPresent(body -> {
                body.getStatements().forEach(stmt -> {
                    log.info("    Statement: {}", stmt.getClass().getSimpleName());
                    if (stmt instanceof ExpressionStmt) {
                        log.info("      Expression: {}", ((ExpressionStmt) stmt).getExpression());
                    }
                });
            });
            super.visit(n, arg);
        }
    }
} 