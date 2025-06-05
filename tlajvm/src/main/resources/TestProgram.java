public class TestProgram {
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