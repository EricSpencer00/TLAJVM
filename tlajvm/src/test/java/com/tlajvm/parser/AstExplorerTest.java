package com.tlajvm.parser;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import org.junit.jupiter.api.Test;

import java.io.FileInputStream;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class AstExplorerTest {
    @Test
    void testParseSimpleProgram() throws IOException {
        // Get the path to the example Java file
        Path filePath = Paths.get("src", "main", "java", "com", "tlajvm", "parser", "MySimpleProgram.java");
        
        // Parse the Java file
        try (FileInputStream in = new FileInputStream(filePath.toFile())) {
            CompilationUnit cu = StaticJavaParser.parse(in);
            
            // Verify that we have a class named MySimpleProgram
            assertTrue(cu.findFirst(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                    .map(c -> c.getNameAsString().equals("MySimpleProgram"))
                    .orElse(false));
            
            // Collect all method names
            List<String> methodNames = new ArrayList<>();
            cu.findAll(MethodDeclaration.class).forEach(m -> methodNames.add(m.getNameAsString()));
            
            // Verify that we have a main method
            assertTrue(methodNames.contains("main"));
        }
    }
} 