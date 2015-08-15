package basic;

import org.lwjgl.LWJGLException;
import org.lwjgl.openal.AL;
import org.lwjgl.opengl.Display;
import org.lwjgl.opengl.DisplayMode;
import org.lwjgl.opengl.GL11;
import org.newdawn.slick.Color;

public class Main {
	private int width, height;
	
	private void initGL() {
        try {
        	DisplayMode m = new DisplayMode(800, 600);
        	width = m.getWidth();
        	height = m.getHeight();
            Display.setDisplayMode(m);
            Display.setTitle("Super Dank Wizzle Dizzle Game With relaxing music Pre-Alpha v0.22 pre-order now for 95$");
            Display.create();
            Display.setVSyncEnabled(true);
        } catch (LWJGLException e) {
            e.printStackTrace();
            System.exit(0);
        }

        GL11.glShadeModel(GL11.GL_SMOOTH);
            // enable alpha blending
            GL11.glEnable(GL11.GL_BLEND);
            GL11.glBlendFunc(GL11.GL_SRC_ALPHA, GL11.GL_ONE_MINUS_SRC_ALPHA);
	        
            GL11.glViewport(0,0,width,height);
        GL11.glMatrixMode(GL11.GL_MODELVIEW);
 
        GL11.glMatrixMode(GL11.GL_PROJECTION);
        GL11.glLoadIdentity();
        GL11.glOrtho(0, width, height, 0, 1, -1);
        GL11.glMatrixMode(GL11.GL_MODELVIEW);
    }
	
    public void start() {
        initGL();  
        Util.drawTexture(400f, 100f, width/2, height/2, 0f, new Textures().getTexture("Menu/Loading"), Color.red);
        Display.update();
        
        Board board = new Board(width, height);

        while (!Display.isCloseRequested()) {   	
        	GL11.glClear(GL11.GL_COLOR_BUFFER_BIT | GL11.GL_DEPTH_BUFFER_BIT); 
        	GL11.glLoadIdentity();	
        	GL11.glTranslatef(-board.getCamX(), -board.getCamY(), 0);
        	board.Tick();
            Display.update();
            Display.sync(60);
        }        
        Display.destroy();
        AL.destroy();
        System.exit(0);
    }
     
    public static void main(String[] argv) {
        Main main = new Main();
        main.start();
    }
}