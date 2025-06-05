package com.tlajvm.parser;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class TlaSpecGeneratorTest {

    @TempDir
    Path tempDir;
    
    private Path outputDir;

    @BeforeEach
    void setUp() throws IOException {
        outputDir = tempDir.resolve("tla-specs");
        Files.createDirectories(outputDir);
    }

    @Test
    void testGenerateSpecForSimpleProgram() throws IOException {
        // Arrange
        String javaCode = """
            public class SimpleProgram {
                private int x;
                private boolean flag;
                
                public void main() {
                    x = 0;
                    flag = true;
                    if (flag) {
                        x = x + 1;
                    }
                }
            }
            """;
        CompilationUnit cu = StaticJavaParser.parse(javaCode);
        Path outputPath = outputDir.resolve("SimpleProgram.tla");
        TlaSpecGenerator generator = new TlaSpecGenerator();

        // Act
        generator.generateSpec(cu, outputPath);

        // Assert
        assertTrue(Files.exists(outputPath));
        List<String> lines = Files.readAllLines(outputPath);
        
        // Print the actual output for debugging
        System.out.println("\nGenerated TLA+ specification for SimpleProgram:");
        lines.forEach(System.out::println);
        
        // Check module declaration
        assertTrue(lines.stream().anyMatch(line -> line.contains("---- MODULE SimpleProgram ----")));
        
        // Check EXTENDS clause
        assertTrue(lines.stream().anyMatch(line -> line.contains("EXTENDS Naturals, Sequences")));
        
        // Check variables
        assertTrue(lines.stream().anyMatch(line -> line.contains("VARIABLE pc")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("VARIABLE x")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("VARIABLE flag")));
        
        // Check Init predicate
        assertTrue(lines.stream().anyMatch(line -> line.contains("Init ==")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("pc = 0")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("x = 0")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("flag = FALSE")));
        
        // Check Next predicate
        assertTrue(lines.stream().anyMatch(line -> line.contains("Next ==")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("Step0")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("Step1")));
    }

    @Test
    void testGenerateSpecForComplexProgram() throws IOException {
        // Arrange
        String javaCode = """
            public class ComplexProgram {
                private int counter;
                private boolean isRunning;
                
                public void process() {
                    counter = 0;
                    isRunning = true;
                    while (isRunning) {
                        if (counter < 10) {
                            counter = counter + 1;
                        } else {
                            isRunning = false;
                        }
                    }
                }
            }
            """;
        CompilationUnit cu = StaticJavaParser.parse(javaCode);
        Path outputPath = outputDir.resolve("ComplexProgram.tla");
        TlaSpecGenerator generator = new TlaSpecGenerator();

        // Act
        generator.generateSpec(cu, outputPath);

        // Assert
        assertTrue(Files.exists(outputPath));
        List<String> lines = Files.readAllLines(outputPath);
        
        // Print the actual output for debugging
        System.out.println("\nGenerated TLA+ specification for ComplexProgram:");
        lines.forEach(System.out::println);
        
        // Check module declaration
        assertTrue(lines.stream().anyMatch(line -> line.contains("---- MODULE ComplexProgram ----")));
        
        // Check variables
        assertTrue(lines.stream().anyMatch(line -> line.contains("VARIABLE counter")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("VARIABLE isRunning")));
        
        // Check Init predicate
        assertTrue(lines.stream().anyMatch(line -> line.contains("Init ==")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("counter = 0")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("isRunning = FALSE")));
        
        // Check Next predicate with loop
        assertTrue(lines.stream().anyMatch(line -> line.contains("Next ==")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("Step0")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("isRunning")));
        
        // Check invariants
        assertTrue(lines.stream().anyMatch(line -> line.contains("Invariants ==")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("pc >= 0")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("counter \\in Nat")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("isRunning \\in BOOLEAN")));
        
        // Check temporal properties
        assertTrue(lines.stream().anyMatch(line -> line.contains("TemporalProperties ==")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("WF_vars(pc)")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("WF_vars(counter)")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("WF_vars(isRunning)")));
    }

    @Test
    void testGenerateSpecWithMethodCalls() throws IOException {
        // Arrange
        String javaCode = """
            public class MethodProgram {
                private int value;
                
                public void increment() {
                    value = value + 1;
                }
                
                public void process() {
                    increment();
                    if (value > 0) {
                        increment();
                    }
                }
            }
            """;
        CompilationUnit cu = StaticJavaParser.parse(javaCode);
        Path outputPath = outputDir.resolve("MethodProgram.tla");
        TlaSpecGenerator generator = new TlaSpecGenerator();

        // Act
        generator.generateSpec(cu, outputPath);

        // Assert
        assertTrue(Files.exists(outputPath));
        List<String> lines = Files.readAllLines(outputPath);
        
        // Print the actual output for debugging
        System.out.println("\nGenerated TLA+ specification for MethodProgram:");
        lines.forEach(System.out::println);
        
        // Check module declaration
        assertTrue(lines.stream().anyMatch(line -> line.contains("---- MODULE MethodProgram ----")));
        
        // Check variables
        assertTrue(lines.stream().anyMatch(line -> line.contains("VARIABLE value")));
        
        // Check Init predicate
        assertTrue(lines.stream().anyMatch(line -> line.contains("Init ==")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("value = 0")));
        
        // Check Next predicate with method calls
        assertTrue(lines.stream().anyMatch(line -> line.contains("Next ==")));
        assertTrue(lines.stream().anyMatch(line -> line.contains("value' = value + 1")));
    }
} 