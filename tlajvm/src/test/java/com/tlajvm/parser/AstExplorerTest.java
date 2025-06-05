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
    public void testParseSimpleProgram() {
        AstExplorer explorer = new AstExplorer();
        CompilationUnit cu = explorer.parseJavaFile("src/main/java/com/tlajvm/parser/TestProgram.java");
        assertNotNull(cu);
    }
} 