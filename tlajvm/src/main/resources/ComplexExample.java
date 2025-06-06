public class ComplexExample {
    private int[] numbers;
    private boolean[][] flags;
    private int sum;
    private boolean isProcessing;
    
    public ComplexExample() {
        numbers = new int[3];
        flags = new boolean[3][3];
        sum = 0;
        isProcessing = true;
        
        // Initialize arrays
        for (int i = 0; i < numbers.length; i++) {
            numbers[i] = i * 2;
            for (int j = 0; j < flags[i].length; j++) {
                flags[i][j] = (i + j) % 2 == 0;
            }
        }
    }
    
    public void process() {
        while (isProcessing) {
            // Process each number
            for (int i = 0; i < numbers.length; i++) {
                if (numbers[i] > 0) {
                    incrementSum(numbers[i]);
                    if (checkFlags(i)) {
                        numbers[i] = numbers[i] - 1;
                    }
                }
            }
            
            // Check if we should stop
            if (sum >= 10) {
                isProcessing = false;
            }
        }
    }
    
    private void incrementSum(int value) {
        sum = sum + value;
    }
    
    private boolean checkFlags(int row) {
        boolean result = true;
        for (int j = 0; j < flags[row].length; j++) {
            if (!flags[row][j]) {
                result = false;
                break;
            }
        }
        return result;
    }
    
    public static void main(String[] args) {
        ComplexExample example = new ComplexExample();
        example.process();
    }
} 