import java.io.IOException;
import java.util.ArrayList;
import java.util.concurrent.CopyOnWriteArrayList;

import org.newdawn.slick.openal.Audio;
import org.newdawn.slick.openal.AudioLoader;
import org.newdawn.slick.util.ResourceLoader;


public class Data {
	public static CopyOnWriteArrayList<Cube3D> cubes;
	public static ArrayList<Tile> waypoints;
	public static int[][][] tiles = new int[300][300][300];
	public static Audio[] audio = new Audio[20];
	
	public static void init() {
		cubes = new CopyOnWriteArrayList<Cube3D>();
		waypoints = new ArrayList<Tile>();
		try {
			audio[0] = AudioLoader.getAudio("OGG", ResourceLoader.getResourceAsStream("Sounds/cave.ogg"));
			audio[1] = AudioLoader.getAudio("OGG", ResourceLoader.getResourceAsStream("Sounds/WormHit.ogg"));
			audio[2] = AudioLoader.getAudio("OGG", ResourceLoader.getResourceAsStream("Sounds/Jump.ogg"));
			audio[3] = AudioLoader.getAudio("OGG", ResourceLoader.getResourceAsStream("Sounds/WormHurt.ogg"));
			audio[5] = AudioLoader.getAudio("OGG", ResourceLoader.getResourceAsStream("Sounds/WormDie.ogg"));
			audio[6] = AudioLoader.getAudio("OGG", ResourceLoader.getResourceAsStream("Sounds/Gun1.ogg"));
			audio[7] = AudioLoader.getAudio("OGG", ResourceLoader.getResourceAsStream("Sounds/WormIdle1.ogg"));
			audio[8] = AudioLoader.getAudio("OGG", ResourceLoader.getResourceAsStream("Sounds/WormIdle2.ogg"));
			audio[9] = AudioLoader.getAudio("OGG", ResourceLoader.getResourceAsStream("Sounds/WormSpawn.ogg"));
			audio[10] = AudioLoader.getAudio("OGG", ResourceLoader.getResourceAsStream("Sounds/WormRareSpawn.ogg"));
			audio[11] = AudioLoader.getAudio("OGG", ResourceLoader.getResourceAsStream("Sounds/cave2.ogg"));
			audio[12] = AudioLoader.getAudio("OGG", ResourceLoader.getResourceAsStream("Sounds/Welcome.ogg"));
			audio[13] = AudioLoader.getAudio("OGG", ResourceLoader.getResourceAsStream("Sounds/BlastShoot.ogg"));
			audio[14] = AudioLoader.getAudio("OGG", ResourceLoader.getResourceAsStream("Sounds/BlastHit.ogg"));
			audio[16] = AudioLoader.getAudio("OGG", ResourceLoader.getResourceAsStream("Sounds/Die.ogg"));
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public static void updateData() {
		
	}
}
