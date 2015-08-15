import java.io.FileInputStream;
import java.io.IOException;

import org.newdawn.slick.opengl.Texture;
import org.newdawn.slick.opengl.TextureLoader;


public class TexLoad {
	public static Texture[] tex = new Texture[90];
	
	public static void init() {
		try {
			
			tex[0] = TextureLoader.getTexture("PNG", new FileInputStream("Texture/Stone.png"));
			tex[1] = TextureLoader.getTexture("PNG", new FileInputStream("Texture/SmoothStone.png"));
			tex[2] = TextureLoader.getTexture("PNG", new FileInputStream("Texture/Red.png"));
			tex[3] = TextureLoader.getTexture("BMP", new FileInputStream("Texture/Glass.bmp"));
			tex[4] = TextureLoader.getTexture("PNG", new FileInputStream("Texture/Green.png"));
			tex[5] = TextureLoader.getTexture("PNG", new FileInputStream("Texture/Face.png"));
			tex[6] = TextureLoader.getTexture("PNG", new FileInputStream("Texture/WormBody.png"));
			tex[7] = TextureLoader.getTexture("PNG", new FileInputStream("Texture/WormHead.png"));
			tex[8] = TextureLoader.getTexture("PNG", new FileInputStream("Texture/WormName.png"));
			tex[9] = TextureLoader.getTexture("PNG", new FileInputStream("Texture/Bar.png"));
			tex[10] = TextureLoader.getTexture("PNG", new FileInputStream("Texture/Warning.png"));
			tex[11] = TextureLoader.getTexture("PNG", new FileInputStream("Texture/BG.png"));
			tex[12] = TextureLoader.getTexture("PNG", new FileInputStream("Texture/Blast.png"));
			tex[13] = TextureLoader.getTexture("PNG", new FileInputStream("Texture/Feature.png"));
		} catch (IOException e) {
			e.printStackTrace();
			System.exit(0);
		}
	}
}
