package com.tlajvm.parser;

public class ComplexProgram {
    private int counter;
    private boolean isRunning;
    
    public ComplexProgram() {
        this.counter = 0;
        this.isRunning = true;
    }
    
    public void process() {
        while (isRunning && counter < 5) {
            if (counter % 2 == 0) {
                incrementCounter();
            } else {
                decrementCounter();
            }
            checkStatus();
        }
    }
    
    private void incrementCounter() {
        counter++;
        System.out.println("Counter incremented: " + counter);
    }
    
    private void decrementCounter() {
        counter--;
        System.out.println("Counter decremented: " + counter);
    }
    
    private void checkStatus() {
        if (counter >= 5) {
            isRunning = false;
        }
    }
    
    public static void main(String[] args) {
        ComplexProgram program = new ComplexProgram();
        program.process();
    }
} 