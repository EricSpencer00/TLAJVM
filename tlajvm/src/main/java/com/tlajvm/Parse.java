package com.tlajvm;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import java.io.FileInputStream;
import java.io.FileNotFoundException;

public class Parse {
    public static void main(String[] args) {
        try {
            // Use the sample file from resources
            FileInputStream in = new FileInputStream("src/main/resources/Sample.java");
            CompilationUnit cu = StaticJavaParser.parse(in);
            
            // Visit and print the methods
            new MethodVisitor().visit(cu, null);
            
        } catch (FileNotFoundException e) {
            System.err.println("Error: Could not find the Java file to parse.");
            e.printStackTrace();
        }
    }

    private static class MethodVisitor extends VoidVisitorAdapter<Void> {
        @Override
        public void visit(MethodDeclaration n, Void arg) {
            System.out.println("Method: " + n.getName());
            n.getBody().ifPresent(body -> {
                body.getStatements().forEach(stmt -> {
                    if (stmt instanceof ExpressionStmt) {
                        System.out.println("      Expression: " + ((ExpressionStmt) stmt).getExpression());
                    }
                });
            });
            super.visit(n, arg);
        }
    }
}