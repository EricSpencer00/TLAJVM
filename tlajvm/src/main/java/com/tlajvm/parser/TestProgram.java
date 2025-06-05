package com.tlajvm.parser;

public class TestProgram {
    private int counter = 0;
    private boolean isRunning = true;
    private int[] values = new int[3];

    public TestProgram() {
        for (int i = 0; i < values.length; i++) {
            values[i] = i;
        }
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
        TestProgram program = new TestProgram();
        program.process();
    }
} 