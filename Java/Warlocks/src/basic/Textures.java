package basic;
import java.io.IOException;
import java.util.HashMap;

import org.newdawn.slick.opengl.Texture;
import org.newdawn.slick.opengl.TextureLoader;
import org.newdawn.slick.util.ResourceLoader;

public class Textures {
	private HashMap<String, Texture> textures;
	
	public Textures() {
		textures = new HashMap<String, Texture>();
	}
	
	public Texture getTexture(String t) {
		if (textures.containsKey(t)) {
			return textures.get(t);
		}
		
		Texture tex = null;
		
		try {
			tex = TextureLoader.getTexture("PNG", ResourceLoader.getResourceAsStream("Sprites/"+t+".png"));
			textures.put(t, tex);
		} catch (IOException e) {
			e.printStackTrace();
		}		
		
		return tex;	
	}
}
