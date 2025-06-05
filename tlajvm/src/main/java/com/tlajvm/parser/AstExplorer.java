package com.tlajvm.parser;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import java.io.FileInputStream;
import java.io.IOException;

public class AstExplorer {
    public CompilationUnit parseJavaFile(String filePath) {
        try (FileInputStream in = new FileInputStream(filePath)) {
            return StaticJavaParser.parse(in);
        } catch (IOException e) {
            throw new RuntimeException("Error parsing Java file: " + filePath, e);
        }
    }
} 