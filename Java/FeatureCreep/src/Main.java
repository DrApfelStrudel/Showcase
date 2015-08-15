import static org.lwjgl.opengl.GL11.GL_ALPHA_TEST;
import static org.lwjgl.opengl.GL11.GL_BLEND;
import static org.lwjgl.opengl.GL11.GL_DEPTH_TEST;
import static org.lwjgl.opengl.GL11.GL_NICEST;
import static org.lwjgl.opengl.GL11.GL_ONE_MINUS_SRC_ALPHA;
import static org.lwjgl.opengl.GL11.GL_PERSPECTIVE_CORRECTION_HINT;
import static org.lwjgl.opengl.GL11.GL_SRC_ALPHA;
import static org.lwjgl.opengl.GL11.GL_TEXTURE_2D;
import static org.lwjgl.opengl.GL11.glBlendFunc;
import static org.lwjgl.opengl.GL11.glEnable;
import static org.lwjgl.opengl.GL11.glHint;
import static org.lwjgl.opengl.GL11.glLoadIdentity;

import java.awt.Dimension;
import java.awt.Font;
import java.awt.Toolkit;
import java.io.FileInputStream;
import java.io.IOException;

import org.lwjgl.BufferUtils;
import org.lwjgl.LWJGLException;
import org.lwjgl.input.Cursor;
import org.lwjgl.input.Mouse;
import org.lwjgl.openal.AL;
import org.lwjgl.opengl.Display;
import org.lwjgl.opengl.DisplayMode;
import org.lwjgl.opengl.GL11;
import org.lwjgl.util.glu.GLU;
import org.newdawn.slick.Color;
import org.newdawn.slick.TrueTypeFont;
import org.newdawn.slick.openal.SoundStore;
import org.newdawn.slick.opengl.Texture;
import org.newdawn.slick.opengl.TextureLoader;
import org.newdawn.slick.util.ResourceLoader;

public class Main {
	
	private static DisplayMode[] modes;
	public static DisplayMode mode;
	private static int fps = 60;
	
	/**
	 * Set the display mode to be used 
	 * 
	 * @param width The width of the display required
	 * @param height The height of the display required
	 * @param fullscreen True if we want fullscreen mode
	 */
	public static void setDisplayMode(int width, int height, boolean fullscreen) {

	    // return if requested DisplayMode is already set
	    if ((Display.getDisplayMode().getWidth() == width) && 
	        (Display.getDisplayMode().getHeight() == height) && 
		(Display.isFullscreen() == fullscreen)) {
		    return;
	    }

	    try {
	        DisplayMode targetDisplayMode = null;
			
		if (fullscreen) {
		    DisplayMode[] modes = Display.getAvailableDisplayModes();
		    int freq = 0;
					
		    for (int i=0;i<modes.length;i++) {
		        DisplayMode current = modes[i];
						
			if ((current.getWidth() == width) && (current.getHeight() == height)) {
			    if ((targetDisplayMode == null) || (current.getFrequency() >= freq)) {
			        if ((targetDisplayMode == null) || (current.getBitsPerPixel() > targetDisplayMode.getBitsPerPixel())) {
				    targetDisplayMode = current;
				    freq = targetDisplayMode.getFrequency();
	                        }
	                    }

			    // if we've found a match for bpp and frequence against the 
			    // original display mode then it's probably best to go for this one
			    // since it's most likely compatible with the monitor
			    if ((current.getBitsPerPixel() == Display.getDesktopDisplayMode().getBitsPerPixel()) &&
	                        (current.getFrequency() == Display.getDesktopDisplayMode().getFrequency())) {
	                            targetDisplayMode = current;
	                            break;
	                    }
	                }
	            }
	        } else {
	            targetDisplayMode = new DisplayMode(width,height);
	        }

	        if (targetDisplayMode == null) {
	            System.out.println("Failed to find value mode: "+width+"x"+height+" fs="+fullscreen);
	            System.exit(0);
	            return;
	        }
	        mode = targetDisplayMode;
			Display.setDisplayMode(mode);
	        Display.setFullscreen(fullscreen);
				
	    } catch (LWJGLException e) {
	        System.out.println("Unable to setup mode "+width+"x"+height+" fullscreen="+fullscreen + e);
	    }
	}
	
	public static void initGL() {
		try {
			Dimension screenSize = Toolkit.getDefaultToolkit().getScreenSize();
			double width = screenSize.getWidth();
			double height = screenSize.getHeight();
			modes = Display.getAvailableDisplayModes();
			setDisplayMode((int)width,(int)height,true);
			Display.setTitle("Feature Creep");
			Display.create();

	        glEnable(GL_TEXTURE_2D);
	        glEnable(GL_BLEND);
	        glEnable(GL_ALPHA_TEST);
	        glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
	        glHint(GL_PERSPECTIVE_CORRECTION_HINT, GL_NICEST);
	        glEnable(GL11.GL_CULL_FACE);
	        GL11.glCullFace(GL11.GL_FRONT);

		} catch (LWJGLException e) {
			e.printStackTrace();
		}
	}
	
	public static void main(String[] args) {
		GameBoard g = new GameBoard();
		
		initGL();
		
		TexLoad.init();
		GL11.glMatrixMode(GL11.GL_PROJECTION); 
		GL11.glLoadIdentity(); 
		GL11.glOrtho(0, Main.mode.getWidth(), Main.mode.getHeight(), 0, -1, 1);
		GL11.glMatrixMode(GL11.GL_MODELVIEW); 
		GL11.glLoadIdentity();
		GL11.glDisable(GL11.GL_DEPTH_TEST);

		TexLoad.tex[5].bind();
		GL11.glTexParameteri(GL_TEXTURE_2D, GL11.GL_TEXTURE_MAG_FILTER, GL11.GL_NEAREST);
		GL11.glBegin(GL11.GL_QUADS);
			GL11.glTexCoord2f(0, 0);
			GL11.glVertex2f(100, 100);
			GL11.glTexCoord2f(1, 0);
			GL11.glVertex2f(mode.getWidth()-100, 100);
			GL11.glTexCoord2f(1, 1);
			GL11.glVertex2f(mode.getWidth()-100, mode.getHeight()-100);
			GL11.glTexCoord2f(0, 1);
			GL11.glVertex2f(100, mode.getHeight()-100);
		GL11.glEnd();

		SoundStore.get().poll(0);
		Display.update();
		Display.sync(60);
				
		g.init();
		
		while (!Display.isCloseRequested()) {

			g.update();
			
			GL11.glClear(GL11.GL_COLOR_BUFFER_BIT | GL11.GL_DEPTH_BUFFER_BIT);
			GL11.glTexParameteri(GL_TEXTURE_2D, GL11.GL_TEXTURE_MAG_FILTER, GL11.GL_NEAREST);
			
			GL11.glMatrixMode(GL11.GL_PROJECTION);
			GL11.glLoadIdentity();
			GLU.gluPerspective(70.0f, mode.getWidth()/mode.getHeight(), 0.1f, 1000);
			GL11.glMatrixMode(GL11.GL_MODELVIEW);
	        	glLoadIdentity();
	        	glEnable(GL_DEPTH_TEST);
	
			GL11.glPushMatrix();
			GL11.glRotatef(g.getPlayer().getCam().getRotX(), 1, 0, 0);
			GL11.glRotatef(g.getPlayer().getCam().getRotY(), 0, 1, 0);
			GL11.glRotatef(g.getPlayer().getCam().getRotZ(), 0, 0, 1);
			GL11.glTranslatef(-g.getPlayer().getCam().getX(),-g.getPlayer().getCam().getY(),-g.getPlayer().getCam().getZ());
			
			//3D Stuff
			
			g.ThreeDeeRender();
				
			GL11.glPopMatrix();
			
			GL11.glMatrixMode(GL11.GL_PROJECTION); 
			GL11.glLoadIdentity(); 
			GL11.glOrtho(0, mode.getWidth(), mode.getHeight(), 0, -1, 1);
			GL11.glMatrixMode(GL11.GL_MODELVIEW); 
			GL11.glLoadIdentity();
			GL11.glDisable(GL11.GL_DEPTH_TEST);
			
			//2D Stuff
			
			g.TwoDeeRender();


			SoundStore.get().poll(0);
			Display.update();
			Display.sync(fps);
			
		}

		AL.destroy();
		Display.destroy();
		System.exit(0);
	}
}

