package be.unamur.info.b314.compiler;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

/**
 * Simple debug utility to compare the output of CodeGenVisitorST with expected output
 */
public class CodeGenDebug {
    public static void main(String[] args) throws IOException {
        // Create a new code generator
        CodeGenVisitorST codeGen = new CodeGenVisitorST();
        
        // Generate the code
        String generatedCode = codeGen.visit(null);
        
        // Read the expected output
        String expectedCode = new String(Files.readAllBytes(
            Paths.get("src/test/resources/expected/expected_basic.py")));
        
        // Print both for comparison
        System.out.println("=== GENERATED CODE ===");
        System.out.println(generatedCode);
        System.out.println("\n=== EXPECTED CODE ===");
        System.out.println(expectedCode);
        
        // Compare character by character to find differences
        System.out.println("\n=== DIFFERENCES ===");
        if (generatedCode.equals(expectedCode)) {
            System.out.println("No differences found! The strings are identical.");
        } else {
            int len1 = generatedCode.length();
            int len2 = expectedCode.length();
            System.out.println("String lengths: Generated=" + len1 + ", Expected=" + len2);
            
            int minLength = Math.min(len1, len2);
            boolean differenceFound = false;
            
            for (int i = 0; i < minLength; i++) {
                char c1 = generatedCode.charAt(i);
                char c2 = expectedCode.charAt(i);
                
                if (c1 != c2) {
                    differenceFound = true;
                    System.out.println("Difference at position " + i + ": '" + c1 + "' (Unicode " + 
                                      (int)c1 + ") vs '" + c2 + "' (Unicode " + (int)c2 + ")");
                    
                    // Show context around the difference
                    int contextStart = Math.max(0, i - 20);
                    int contextEnd = Math.min(minLength, i + 20);
                    
                    System.out.println("Context in generated: \"" + 
                                      generatedCode.substring(contextStart, contextEnd) + "\"");
                    System.out.println("Context in expected: \"" + 
                                      expectedCode.substring(contextStart, contextEnd) + "\"");
                    
                    // Only show the first 5 differences
                    if (differenceFound && i > 5) {
                        System.out.println("... more differences may exist ...");
                        break;
                    }
                }
            }
            
            if (!differenceFound && len1 != len2) {
                System.out.println("The strings differ only in length. One is a prefix of the other.");
                if (len1 < len2) {
                    System.out.println("Extra characters in expected: \"" + 
                                      expectedCode.substring(len1) + "\"");
                } else {
                    System.out.println("Extra characters in generated: \"" + 
                                      generatedCode.substring(len2) + "\"");
                }
            }
        }
    }
}
